#define _GNU_SOURCE
#define __USE_GNU
#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>

static void* (*malloc_func)(size_t size) = NULL;
static void* (*calloc_func)(size_t num, size_t size) = NULL;
static void (*free_func)(void *ptr) = NULL;

void __attribute__((constructor)) init_funcptrs() {
  malloc_func = (void *(*)(size_t)) dlsym(RTLD_NEXT, "malloc");
  calloc_func = (void *(*)(size_t, size_t)) dlsym(RTLD_NEXT, "calloc");
  free_func = (void (*)(void*)) dlsym(RTLD_NEXT, "free");
}

/********************/
/**  Stats  *********/
/********************/

long int alloc_max = 0, alloc_cur = 0;
long int quarantine_size = 0;

/********************/
/**  Tree  **********/
/********************/

typedef struct node{
  struct node * l, * r;
  void *base, *end;
  int refcnt;
  int freed;
} node;

node *rangetree_root = NULL;

node * rangetree_newnode(void *base, void *end) {
  node * n = malloc_func(sizeof(node));
  n->base = base;
  n->end = end;
  n->refcnt = 0;
  n->freed = 0;
  n->l = n->r = NULL;
  return n;
}

void rangetree_insert(node ** root, node * child) {
  if (!*root) {
    *root = child;  // tree root not exists
    return;
  }

  if (child->base <= (*root)->base)
    rangetree_insert( &(*root)->l, child );
  else
    rangetree_insert( &(*root)->r , child );
}

// search the node that addr belongs to
node * rangetree_search(node * root, void *addr) {
  if (root == NULL)
    return NULL;

  if (root->base <= addr
      && addr <= root->end) // allow off-by-1 pointer
    return root;

  if (addr < root->base)
    return rangetree_search(root->l, addr);

  if (root->end < addr)
    return rangetree_search(root->r, addr);

  return NULL;
}


// search and free
void rangetree_free(node **root, void *addr) {
  if (*root == NULL)
    return;

  if ((*root)->base <= addr
      && addr <= (*root)->end) {
    if ((*root)->l == NULL) {
      node *tmp = *root;
      *root = tmp->r;
      return free_func(tmp);
    } else if ((*root)->r == NULL) {
      node *tmp = *root;
      *root = tmp->l;
      return free_func(tmp);
    }

    node *next = (*root)->r;
    if (next->l == NULL) {
      (*root)->base = next->base;
      (*root)->end = next->end;
      (*root)->refcnt = next->refcnt;
      (*root)->r = next->r;
      return free_func(next);
    }

    node *par;
    while (next->l) {
      par = next;
      next = next->l;
    }

    (*root)->base = next->base;
    (*root)->end = next->end;
    (*root)->refcnt = next->refcnt;
    par->l = next->r;
    return free_func(next);
  }

  if (addr < (*root)->base)
    return rangetree_free(&(*root)->l, addr);

  if ((*root)->end < addr)
    return rangetree_free(&(*root)->r, addr);

  printf("[interposer] invalid free !!!!!!\n");
  return;
}

void rangetree_printnode(node *n, int d) {
  while (d--) printf(" ");
  printf("[0x%lx, 0x%lx](0x%lx, %ld)\n", (long int)n->base, (long int)n->end,
         (long int)(n->end - n->base), (long int)(n->end - n->base));
}

void rangetree_print(node *root, int depth) {
  if (root != NULL) {
    rangetree_print(root->l, depth+1);
    rangetree_printnode(root, depth);
    rangetree_print(root->r, depth+1);
  }
}

/********************/
/**  Interposer  ****/
/********************/

int atexit_registered = 0;

void atexit_hook() {
  printf("PROGRAM TERMINATED!\n");
  printf("max alloc: %ld, cur alloc: %ld\n", alloc_max, alloc_cur);
  printf("quarantine: %ld B\n", quarantine_size);
}

static void alloc_common(void *base, void *end) {
  alloc_cur++;
  if (alloc_cur > alloc_max)
    alloc_max = alloc_cur;
  if (!atexit_registered) {
    if (atexit(atexit_hook))
      printf("atexit failed!\n");
    atexit_registered = 1;
  }

  node *new = rangetree_newnode(base, end);
  rangetree_insert(&rangetree_root, new);
}

void *malloc(size_t size)
{
  void *ret;

  ret = malloc_func(size);
  if (!ret)
    printf("[interposer] malloc failed ??????\n");
  alloc_common(ret, ret+size);
  return(ret);
}

void *calloc(size_t num, size_t size)
{
  void *ret;

  ret = calloc_func(num, size);
  if (!ret)
    printf("[interposer] calloc failed ??????\n");
  alloc_common(ret, ret+num*size);
  return(ret);
}

void *realloc(void *ptr, size_t size)
{
  void *ret;

  if (ptr==NULL)
    return malloc(size);

  node *orig = rangetree_search(rangetree_root, ptr);
  if (orig->base != ptr)
    printf("[interposer] ptr != base in realloc ??????\n");
  if ((ptr+size) <= orig->end)
    return ptr;
  /* { */
  /*   static void* (*realloc_func)(void *ptr, size_t size) = NULL; */
  /*   if(!realloc_func) */
  /*     realloc_func = (void *(*)(void *, size_t)) dlsym(RTLD_NEXT, "realloc"); */
  /*   ret = realloc_func(ptr, size); */
  /*   return(ret); */
  /* } */

  // just malloc
  ret = malloc(size);
  memcpy(ret, ptr, orig->end - orig->base);
  free(ptr);
  return(ret);
}

void free(void *ptr)
{
  node *n = rangetree_search(rangetree_root, ptr);
  if (n->freed)
    printf("[interposer] double free??????\n");

  if (n->refcnt == 0) {
    free_func(ptr);
  } else {
    n->freed = 1;
    quarantine_size += (n->end - n->base);
  }

  alloc_cur--;
}


/*****************************/
/**  Refcnt modification  ****/
/*****************************/

void ls_inc_refcnt(char *p) {
  node *n = rangetree_search(rangetree_root, p);
  if (n)
    ++n->refcnt;
}

void ls_dec_refcnt(char *p) {
  node *n = rangetree_search(rangetree_root, p);
  if (n) { // is heap node
    if (n->refcnt==0)
      printf("[interposer] refcnt is already zero???\n");
    --n->refcnt;
    if (n->refcnt==0) {
      if (n->freed) { // marked to be freed
        quarantine_size -= (n->end - n->base);
        free_func(n->base);
      }
      rangetree_free(&rangetree_root, p);
    }
  }
}
