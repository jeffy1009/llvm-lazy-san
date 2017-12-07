#define _GNU_SOURCE
#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>

long int alloc_max = 0, alloc_cur = 0;
long int quarantine_size = 0;

static void* (*malloc_func)(size_t size) = NULL;
static void* (*calloc_func)(size_t num, size_t size) = NULL;
static void (*free_func)(void *ptr) = NULL;

void atexit_hook() {
  printf("PROGRAM TERMINATED!\n");
  printf("max alloc: %ld, cur alloc: %ld\n", alloc_max, alloc_cur);
  printf("quarantine: %ld B\n", quarantine_size);
}

void __attribute__((constructor)) init_funcptrs() {
  malloc_func = (void *(*)(size_t)) dlsym(RTLD_NEXT, "malloc");
  calloc_func = (void *(*)(size_t, size_t)) dlsym(RTLD_NEXT, "calloc");
  free_func = (void (*)(void*)) dlsym(RTLD_NEXT, "free");

  if (atexit(atexit_hook))
    printf("atexit failed!\n");
}

/********************/
/**  Tree  **********/
/********************/

typedef struct node{
  struct node * l, * r;
  char *base, *end;
  int refcnt;
  int freed;
} node;

node *rangetree_root = NULL;

node * rangetree_newnode(char *base, char *end) {
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
    *root = child;  /* tree root not exists */
    return;
  }

  if (child->base <= (*root)->base)
    rangetree_insert( &(*root)->l, child );
  else
    rangetree_insert( &(*root)->r , child );
}

/* search the node that addr belongs to */
node * rangetree_search(node * root, char *addr) {
  if (root == NULL)
    return NULL;

  if (root->base <= addr
      && addr <= root->end) /* allow off-by-1 pointer */
    return root;

  if (addr < root->base)
    return rangetree_search(root->l, addr);

  if (root->end < addr)
    return rangetree_search(root->r, addr);

  return NULL;
}

/* search and free */
void rangetree_free(node **root, char *addr) {
  if (*root == NULL)
    return;

  if ((*root)->base <= addr
      && addr <= (*root)->end) {
    node *next, *par;
    if ((*root)->l == NULL) {
      node *tmp = *root;
      *root = tmp->r;
      free_func(tmp);
      return;
    } else if ((*root)->r == NULL) {
      node *tmp = *root;
      *root = tmp->l;
      free_func(tmp);
      return;
    }

    next = (*root)->r;
    if (next->l == NULL) {
      (*root)->base = next->base;
      (*root)->end = next->end;
      (*root)->refcnt = next->refcnt;
      (*root)->r = next->r;
      free_func(next);
      return;
    }

    while (next->l) {
      par = next;
      next = next->l;
    }

    (*root)->base = next->base;
    (*root)->end = next->end;
    (*root)->refcnt = next->refcnt;
    par->l = next->r;
    free_func(next);
    return;
  }

  if (addr < (*root)->base) {
    rangetree_free(&(*root)->l, addr);
    return;
  }

  if ((*root)->end < addr) {
    rangetree_free(&(*root)->r, addr);
    return;
  }

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

static void alloc_common(char *base, char *end) {
  node *new;

  alloc_cur++;
  if (alloc_cur > alloc_max)
    alloc_max = alloc_cur;

  new = rangetree_newnode(base, end);
  rangetree_insert(&rangetree_root, new);
}

void *malloc(size_t size) {
  char *ret;

  ret = malloc_func(size);
  if (!ret)
    printf("[interposer] malloc failed ??????\n");
  alloc_common(ret, ret+size);
  return(ret);
}

void *calloc(size_t num, size_t size) {
  char *ret;

  ret = calloc_func(num, size);
  if (!ret)
    printf("[interposer] calloc failed ??????\n");
  alloc_common(ret, ret+num*size);
  return(ret);
}

void *realloc(void *ptr, size_t size) {
  char *ret;
  char *p = (char*)ptr;
  node *orig;

  if (p==NULL)
    return malloc(size);

  orig = rangetree_search(rangetree_root, p);
  if (orig->base != p)
    printf("[interposer] ptr != base in realloc ??????\n");
  if ((p+size) <= orig->end)
    return p;
  /* { */
  /*   static void* (*realloc_func)(void *ptr, size_t size) = NULL; */
  /*   if(!realloc_func) */
  /*     realloc_func = (void *(*)(void *, size_t)) dlsym(RTLD_NEXT, "realloc"); */
  /*   ret = realloc_func(ptr, size); */
  /*   return(ret); */
  /* } */

  /* just malloc */
  ret = malloc(size);
  memcpy(ret, p, orig->end - orig->base);
  free(p);
  return(ret);
}

void free(void *ptr) {
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
  if (n) { /* is heap node */
    if (n->refcnt==0)
      printf("[interposer] refcnt is already zero???\n");
    --n->refcnt;
    if (n->refcnt==0) {
      if (n->freed) { /* marked to be freed */
        quarantine_size -= (n->end - n->base);
        free_func(n->base);
      }
      rangetree_free(&rangetree_root, p);
    }
  }
}
