#define _GNU_SOURCE
#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>

long int alloc_max = 0, alloc_cur = 0;
long int quarantine_size = 0, quarantine_max = 0;

static void* (*malloc_func)(size_t size) = NULL;
static void* (*calloc_func)(size_t num, size_t size) = NULL;
static void (*free_func)(void *ptr) = NULL;

void ls_dec_refcnt(char *p);

void atexit_hook() {
  printf("PROGRAM TERMINATED!\n");
  printf("max alloc: %ld, cur alloc: %ld\n", alloc_max, alloc_cur);
  printf("quarantine max: %ld B, cur: %ld B\n", quarantine_max, quarantine_size);
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
  long int ptrlog[0];
} node;

node *rangetree_root = NULL;

node * rangetree_newnode(char *base, char *end) {
  node * n;
  long int size = end - base;
  long int ptrlog_size = ((size + 8*64 - 1)/(8*64))*8;

  n = malloc_func(sizeof(node) + ptrlog_size);
  n->base = base;
  n->end = end;
  n->refcnt = 0;
  n->freed = 0;
  n->l = n->r = NULL;
  memset(n->ptrlog, 0, ptrlog_size);
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
  node *tmp_root;

  if (*root == NULL)
    return;

  tmp_root = *root;
  if ((*root)->base <= addr
      && addr <= (*root)->end) {
    node *next, *par;
    if ((*root)->l == NULL) {
      *root = tmp_root->r;
      free_func(tmp_root);
      return;
    } else if ((*root)->r == NULL) {
      *root = tmp_root->l;
      free_func(tmp_root);
      return;
    }

    next = (*root)->r;
    if (next->l == NULL) {
      next->l = tmp_root->l;
      *root = next;
      free_func(tmp_root);
      return;
    }

    while (next->l) {
      par = next;
      next = next->l;
    }

    par->l = next->r;
    next->l = tmp_root->l;
    next->r = tmp_root->r;
    *root = next;
    free_func(tmp_root);
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
  printf("0x%lx:[0x%lx, 0x%lx](0x%lx, %ld)#%d%s\n", (long int)n,
         (long int)n->base, (long int)n->end,
         (long int)(n->end - n->base), (long int)(n->end - n->base),
         n->refcnt, n->freed ? "F" : "");
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

  if (quarantine_size > quarantine_max)
    quarantine_max = quarantine_size;

  new = rangetree_newnode(base, end);
  rangetree_insert(&rangetree_root, new);
}

void *malloc(size_t size) {
  char *ret;

  ret = malloc_func(size);
  if (!ret)
    printf("[interposer] malloc failed ??????\n");
  alloc_common(ret, ret+size);
  memset(ret, 0, size);
  return(ret);
}

void *calloc(size_t num, size_t size) {
  char *ret;

  ret = calloc_func(num, size);
  if (!ret)
    printf("[interposer] calloc failed ??????\n");
  alloc_common(ret, ret+num*size);
  memset(ret, 0, num*size);
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
  node *n;
  long int size;
  long int *p, *p_end;
  long int nword = 0;

  alloc_cur--;

  n = rangetree_search(rangetree_root, ptr);
  if (!n) {
    /* there are no dangling pointers to this node,
       so the node is already removed from the rangetree */
    /* NOTE: there can be a dangling pointer in the register
       and that register value could later be stored in memory.
       Should we handle this case?? */
    free_func(ptr);
    return;
  }

  if (n->freed)
    printf("[interposer] double free??????\n");

  size = n->end - n->base;
  p_end = n->ptrlog + (size+8*64-1)/8/64;
  for (p = n->ptrlog; p < p_end; p++, nword++) {
    while (*p) {
      long int field_offset = 64*nword + __builtin_ctz(*p);
      ls_dec_refcnt((char*)*((long int*)n->base + field_offset));
      *p = *p & (*p - 1); /* unset rightmost bit */
    }
  }

  if (n->refcnt == 0) {
    free_func(ptr);
    rangetree_free(&rangetree_root, ptr);
  } else {
    n->freed = 1;
    quarantine_size += (n->end - n->base);
  }
}


/*****************************/
/**  Refcnt modification  ****/
/*****************************/

/* p - written pointer value
   dest - store destination */
void ls_inc_refcnt(char *p, char *dest) {
  node *n;

  if (!p)
    return;

  n = rangetree_search(rangetree_root, p);
  if (n)
    ++n->refcnt;

  /* mark pointer type field */
  n = rangetree_search(rangetree_root, dest);
  if (n) {
    long int field_offset = (dest - n->base)/8;
    long int word = field_offset/64;
    int rem = field_offset%64;
    n->ptrlog[word] |= (1 << rem);
  }
}

void ls_dec_refcnt(char *p) {
  node *n;
  if (!p)
    return;

  n = rangetree_search(rangetree_root, p);
  if (n) { /* is heap node */
    if (n->refcnt==0)
      printf("[interposer] refcnt is already zero???\n");
    --n->refcnt;
    if (n->refcnt==0) {
      if (n->freed) { /* marked to be freed */
        quarantine_size -= (n->end - n->base);
        free_func(n->base);
        rangetree_free(&rangetree_root, p);
      }
      /* if n is not yet freed, the pointer is probably in some
         register. */
    }
  }
}
