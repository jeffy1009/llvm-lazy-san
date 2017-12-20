#define _GNU_SOURCE
#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>
#include "red_black_tree.h"

#define REFCNT_INIT 0

long int alloc_max = 0, alloc_cur = 0;
long int quarantine_size = 0, quarantine_max = 0, quarantine_max_mb = 0;

void* (*malloc_func)(size_t size) = NULL;
void* (*calloc_func)(size_t num, size_t size) = NULL;
void (*free_func)(void *ptr) = NULL;

void atexit_hook() {
  printf("PROGRAM TERMINATED!\n");
  printf("max alloc: %ld, cur alloc: %ld\n", alloc_max, alloc_cur);
  printf("quarantine max: %ld B, cur: %ld B\n", quarantine_max, quarantine_size);
}

void __attribute__((constructor)) init_interposer() {
  malloc_func = (void *(*)(size_t)) dlsym(RTLD_NEXT, "malloc");
  calloc_func = (void *(*)(size_t, size_t)) dlsym(RTLD_NEXT, "calloc");
  free_func = (void (*)(void*)) dlsym(RTLD_NEXT, "free");

  if (atexit(atexit_hook))
    printf("atexit failed!\n");
}

/************************/
/**  Red-Black Tree  ****/
/************************/

typedef struct rb_key_t {
  char *base, *end;
} rb_key;

typedef struct rb_info_t {
  long int size;
  int refcnt;
  short freed;
  short first_inc;
  long int ptrlog[0];
} rb_info;

rb_red_blk_tree *rb_root = NULL;
rb_key tmp_rb_key; /* temporary key used for queries */

rb_key *rb_new_key(char *base, char *end) {
  rb_key *k = malloc_func(sizeof(rb_key));
  k->base = base;
  k->end = end;
  return k;
}

rb_info *rb_new_info(long int size) {
  rb_info *i;
  long int ptrlog_size = ((size + 8*64 - 1)/(8*64))*8;

  i = malloc_func(sizeof(rb_info) + ptrlog_size);
  i->size = size;
  i->refcnt = REFCNT_INIT;
  i->freed = 0;
  i->first_inc = 0;
  memset(i->ptrlog, 0, ptrlog_size);
  return i;
}

void rb_destroy(void* a) { free_func(a); }

int rb_compare(const void *a, const void *b) {
  rb_key *akey = (rb_key*)a, *bkey = (rb_key*)b;

  if ((akey->base <= bkey->base)
      && (bkey->base <= akey->end)) {
    if ((bkey->base != bkey->end)
        && !((akey->end < bkey->base) || (bkey->end < akey->base)))
      printf("[interposer] existing entry with overlaping region!\n");
    return 0;
  }
  if( akey->base > bkey->base) return(1);
  if( akey->base < bkey->base) return(-1);
  return(0);
}

void rb_print_key(const void* a) {
  rb_key *key = (rb_key*)a;
  printf("[0x%lx, 0x%lx]", (long int)key->base, (long int)key->end);
}

void rb_print_info(void* a) {
  rb_info *info = (rb_info*)a;
  printf("(0x%lx, %ld)#%d%s\n",
         info->size, info->size, info->refcnt, info->freed ? "F" : "");
}

void rb_destroy_info(void *a) { free_func(a); }

void __attribute__((constructor)) init_rb_tree() {
  rb_root = RBTreeCreate(rb_compare, rb_destroy, rb_destroy_info,
                          rb_print_key, rb_print_info);
}

/*****************************/
/**  Refcnt modification  ****/
/*****************************/

/* p - written pointer value
   dest - store destination */
void ls_inc_refcnt(char *p, char *dest) {
  rb_red_blk_node *node;

  if (!p)
    return;

  tmp_rb_key.base = tmp_rb_key.end = p;
  node = RBExactQuery(rb_root, &tmp_rb_key);
  if (node) {
    rb_info *info = node->info;
    if (!info->first_inc)
      info->first_inc = 1;
    else if (info->freed && info->refcnt == REFCNT_INIT)
      printf("[interposer] refcnt became alive again??\n");
    ++info->refcnt;
  }

  /* mark pointer type field */
  tmp_rb_key.base = tmp_rb_key.end = dest;
  node = RBExactQuery(rb_root, &tmp_rb_key);
  if (node) {
    rb_key *key = node->key;
    rb_info *info = node->info;
    long int field_offset = (dest - key->base)/8;
    long int word = field_offset/64;
    int rem = field_offset%64;
    info->ptrlog[word] |= (1UL << rem);
  }
}

void ls_dec_refcnt(char *p, char *dummy) {
  rb_red_blk_node *node;

  if (!p)
    return;

  tmp_rb_key.base = tmp_rb_key.end = p;
  node = RBExactQuery(rb_root, &tmp_rb_key);
  if (node) { /* is heap node */
    rb_key *key = node->key;
    rb_info *info = node->info;
    if (info->refcnt<=REFCNT_INIT)
      printf("[interposer] refcnt <= 0???\n");
    --info->refcnt;
    if (info->refcnt<=0) {
      if (info->freed) { /* marked to be freed */
        quarantine_size -= info->size;
        free_func(key->base);
        RBDelete(rb_root, node);
      }
      /* if n is not yet freed, the pointer is probably in some
         register. */
    }
  }
}

/********************/
/**  Interposer  ****/
/********************/

static void alloc_common(char *base, char *end) {
  rb_key *new_key;
  rb_info *new_info;

  alloc_cur++;
  if (alloc_cur > alloc_max)
    alloc_max = alloc_cur;

  if (quarantine_size > quarantine_max) {
    long int quarantine_mb_tmp;
    quarantine_max = quarantine_size;
    quarantine_mb_tmp = quarantine_max/1024/1024;
    if (quarantine_mb_tmp > quarantine_max_mb) {
      quarantine_max_mb = quarantine_mb_tmp;
      printf("[interposer] quarantine_max = %ld MB\n", quarantine_max_mb);
    }
  }

  new_key = rb_new_key(base, end);
  new_info = rb_new_info(end-base);
  RBTreeInsert(rb_root, new_key, new_info);
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
  char *p = (char*)ptr;
  rb_red_blk_node *orig_node;
  rb_key *orig_key, *new_key;
  rb_info *orig_info, *new_info;
  char *ret;
  long int orig_size, ptrlog_size;

  if (p==NULL)
    return malloc(size);

  tmp_rb_key.base = tmp_rb_key.end = p;
  orig_node = RBExactQuery(rb_root, &tmp_rb_key);

  orig_key = orig_node->key;
  if (orig_key->base != p)
    printf("[interposer] ptr != base in realloc ??????\n");
  if ((p+size) <= orig_key->end)
    return p;

  /* { */
  /*   static void* (*realloc_func)(void *ptr, size_t size) = NULL; */
  /*   if(!realloc_func) */
  /*     realloc_func = (void *(*)(void *, size_t)) dlsym(RTLD_NEXT, "realloc"); */
  /*   ret = realloc_func(ptr, size); */
  /*   return(ret); */
  /* } */

  /* just malloc */
  ret = malloc_func(size);
  if (!ret)
    printf("[interposer] malloc failed ??????\n");

  if (quarantine_size > quarantine_max) {
    long int quarantine_mb_tmp;
    quarantine_max = quarantine_size;
    quarantine_mb_tmp = quarantine_max/1024/1024;
    if (quarantine_mb_tmp > quarantine_max_mb) {
      quarantine_max_mb = quarantine_mb_tmp;
      printf("[interposer] quarantine_max = %ld MB\n", quarantine_max_mb);
    }
  }

  orig_info = orig_node->info;
  new_key = rb_new_key(ret, ret+size);
  new_info = rb_new_info(size);
  RBTreeInsert(rb_root, new_key, new_info);

  memset(ret, 0, size);
  memcpy(ret, p, orig_info->size);

  orig_size = orig_info->size;
  ptrlog_size = ((orig_size + 8*64 - 1)/(8*64))*8;
  memcpy(new_info->ptrlog, orig_info->ptrlog, ptrlog_size);

  if (orig_info->freed)
    printf("[interposer] double free??????\n");

  if (orig_info->refcnt <= 0) {
    free_func(p);
    RBDelete(rb_root, orig_node);
  } else {
    orig_info->freed = 1;
    quarantine_size += orig_size;
  }

  return(ret);
}

void free(void *ptr) {
  long int size;
  long int *p, *p_end;
  long int nword = 0;
  rb_red_blk_node *node;
  rb_key *key;
  rb_info *info;

  alloc_cur--;

  tmp_rb_key.base = tmp_rb_key.end = ptr;
  node = RBExactQuery(rb_root, &tmp_rb_key);
  if (!node) {
    /* there are no dangling pointers to this node,
       so the node is already removed from the rangetree */
    /* NOTE: there can be a dangling pointer in the register
       and that register value could later be stored in memory.
       Should we handle this case?? */
    free_func(ptr);
    return;
  }

  key = node->key;
  info = node->info;
  if (info->freed)
    printf("[interposer] double free??????\n");

  size = info->size;
  p_end = info->ptrlog + (size+8*64-1)/8/64;
  for (p = info->ptrlog; p < p_end; p++, nword++) {
    while (*p) {
      long int field_offset = 64*nword + __builtin_ctz(*p);
      ls_dec_refcnt((char*)*((long int*)key->base + field_offset), 0);
      *p = *p & (*p - 1); /* unset rightmost bit */
    }
  }

  if (info->refcnt <= 0) {
    free_func(ptr);
    RBDelete(rb_root, node);
  } else {
    info->freed = 1;
    quarantine_size += info->size;
  }
}
