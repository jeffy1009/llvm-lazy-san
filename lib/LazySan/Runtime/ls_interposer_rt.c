#define _GNU_SOURCE
#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <sys/mman.h>
#include <errno.h>
#include "red_black_tree.h"

#define REFCNT_INIT 0

long *global_ptrlog;

long alloc_max = 0, alloc_cur = 0, alloc_tot = 0;
long num_ptrs = 0;
long quarantine_size = 0, quarantine_max = 0, quarantine_max_mb = 0;

void* (*malloc_func)(size_t size) = NULL;
void* (*calloc_func)(size_t num, size_t size) = NULL;
void* (*realloc_func)(void *ptr, size_t size) = NULL;
void (*free_func)(void *ptr) = NULL;

void atexit_hook() {
  printf("PROGRAM TERMINATED!\n");
  printf("max alloc: %ld, cur alloc: %ld, tot alloc: %ld\n",
         alloc_max, alloc_cur, alloc_tot);
  printf("num ptrs: %ld\n", num_ptrs);
  printf("quarantine max: %ld B, cur: %ld B\n", quarantine_max, quarantine_size);
}

void __attribute__((constructor)) init_interposer() {
  malloc_func = (void *(*)(size_t)) dlsym(RTLD_NEXT, "malloc");
  calloc_func = (void *(*)(size_t, size_t)) dlsym(RTLD_NEXT, "calloc");
  realloc_func = (void *(*)(void *, size_t)) dlsym(RTLD_NEXT, "realloc");
  free_func = (void (*)(void*)) dlsym(RTLD_NEXT, "free");

  if (atexit(atexit_hook))
    printf("atexit failed!\n");

  global_ptrlog = mmap((void*)0x00007fff8000, 0x020000000000 /* 2TB */,
                       PROT_READ | PROT_WRITE,
                       MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED | MAP_NORESERVE,
                       -1, 0);
  if (global_ptrlog == (void*)-1) {
     /* strangely, perror() segfaults */
    printf("[interposer] global_ptrlog mmap failed: errno %d\n", errno);
    exit(0);
  }
  printf("[interposer] global_ptrlog mmap'ed @ 0x%lx\n", (long)global_ptrlog);
}

/************************/
/**  Red-Black Tree  ****/
/************************/

#define RB_INFO_FREED 		0x1
#define RB_INFO_RCBELOWZERO 	0x10000

typedef struct rb_key_t {
  char *base, *end;
} rb_key;

typedef struct rb_info_t {
  long size;
  int refcnt;
  int flags;
} rb_info;

rb_red_blk_tree *rb_root = NULL;
rb_key tmp_rb_key; /* temporary key used for queries */

rb_key *rb_new_key(char *base, char *end) {
  rb_key *k = malloc_func(sizeof(rb_key));
  k->base = base;
  k->end = end;
  return k;
}

rb_info *rb_new_info(long size) {
  rb_info *i;

  i = malloc_func(sizeof(rb_info));
  i->size = size;
  i->refcnt = REFCNT_INIT;
  i->flags = 0;
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
  printf("[0x%lx, 0x%lx]", (long)key->base, (long)key->end);
}

void rb_print_info(void* a) {
  rb_info *info = (rb_info*)a;
  printf("(0x%lx, %ld)#%d%s\n",
         info->size, info->size, info->refcnt,
         (info->flags & RB_INFO_FREED) ? "F" : "");
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
  long offset, widx, bidx;

  if (!p)
    return;

  num_ptrs++;
  tmp_rb_key.base = tmp_rb_key.end = p;
  node = RBExactQuery(rb_root, &tmp_rb_key);
  if (node) {
    rb_info *info = node->info;
    if ((info->flags & RB_INFO_FREED) && info->refcnt == REFCNT_INIT)
      printf("[interposer] refcnt became alive again??\n");
    ++info->refcnt;
  }

  /* mark pointer type field */
  offset = (long)dest >> 3;
  widx = offset >> 6; /* word index */
  bidx = offset & 0x3F; /* bit index */
  global_ptrlog[widx] |= (1UL << bidx);
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
    if (info->refcnt<=REFCNT_INIT && !(info->flags & RB_INFO_RCBELOWZERO)) {
      info->flags |= RB_INFO_RCBELOWZERO;
      printf("[interposer] refcnt <= 0???\n");
    }
    --info->refcnt;
    if (info->refcnt<=0) {
      if (info->flags & RB_INFO_FREED) { /* marked to be freed */
        quarantine_size -= info->size;
        free_func(key->base);
        RBDelete(rb_root, node);
      }
      /* if n is not yet freed, the pointer is probably in some
         register. */
    }
  }
}

void ls_clear_ptrlog(char *p, long size) {
  char *end = p + size;
  long offset = (long)p >> 3, offset_e = (long)end >> 3;
  long widx = offset >> 6, widx_e = offset_e >> 6;
  long bidx = offset & 0x3F, bidx_e = offset_e & 0x3F;
  long *pl = global_ptrlog + widx, *pl_e = global_ptrlog + widx_e;
  long mask = ((1UL << bidx) - 1), mask_e = (-1L << bidx_e);

  if (widx == widx_e) {
    mask |= mask_e;
    *pl &= mask;
    return;
  }

  *pl++ &= mask;
  while (pl < pl_e)
    *pl++ = 0;
  *pl &= mask_e;
}

void ls_copy_ptrlog(char *d, char *s, long size) {
  char *end = d + size;
  long offset = (long)d >> 3, offset_e = (long)end >> 3;
  long s_offset = (long)s >> 3;
  long widx = offset >> 6, widx_e = offset_e >> 6;
  long s_widx = s_offset >> 6;
  long bidx = offset & 0x3F, bidx_e = offset_e & 0x3F;
  long *pl = global_ptrlog + widx, *pl_e = global_ptrlog + widx_e;
  long *s_pl = global_ptrlog + s_widx;
  long mask = ((1UL << bidx) - 1), mask_e = (-1L << bidx_e);
  long s_pl_val;

  if (widx == widx_e) {
    mask |= mask_e;
    s_pl_val = *s_pl & mask; /* should be done before the next
                                in case d and s overlap */
    *pl = (*pl & mask) | s_pl_val;
    return;
  }

  s_pl_val = *s_pl & mask;
  *pl = (*pl & mask) | s_pl_val;
  pl++, s_pl++;
  while (pl < pl_e)
    *pl++ = *s_pl++;
  s_pl_val = *s_pl & mask_e;
  *pl = (*pl & mask_e) | s_pl_val;
}

static void inc_or_dec_ptrlog(char *p, long size, void (*f)(char *, char *)) {
  char *end = p + size;
  long offset = (long)p >> 3, offset_e = (long)end >> 3;
  long widx = offset >> 6, widx_e = offset_e >> 6;
  long bidx = offset & 0x3F, bidx_e = offset_e & 0x3F;
  long *pl = global_ptrlog + widx, *pl_e = global_ptrlog + widx_e;
  long mask_e = (-1L << bidx_e);
  long *pw = (long *)p;
  long pl_val;

  if (widx == widx_e) {
    pl_val = (*pl & ~mask_e) >> bidx;
    while (pl_val) {
      long tmp = __builtin_ctzl(pl_val);
      f((char*)*(pw+tmp), 0);
      pl_val &= (pl_val - 1);
    }
    return;
  }

  pl_val = *pl >> bidx;
  while (pl_val) {
    long tmp = __builtin_ctzl(pl_val);
    f((char*)*(pw+tmp), 0);
    pl_val &= (pl_val - 1);
  }
  pl++, pw+=(64-bidx);

  while (pl < pl_e) {
    pl_val = *pl;
    while (pl_val) {
      long tmp = __builtin_ctzl(pl_val);
      f((char*)*(pw + tmp), 0);
      pl_val &= (pl_val - 1);
    }
    pl++, pw+=64;
  }

  pl_val = *pl & ~mask_e;
  while (pl_val) {
    long tmp = __builtin_ctzl(pl_val);
    f((char*)*(pw + tmp), 0);
    pl_val &= (pl_val - 1);
  }
}

void ls_inc_ptrlog(char *p, long size) {
  inc_or_dec_ptrlog(p, size, ls_inc_refcnt);
}

void ls_dec_ptrlog(char *p, long size) {
  inc_or_dec_ptrlog(p, size, ls_dec_refcnt);
}

/********************/
/**  Interposer  ****/
/********************/

static rb_red_blk_node *alloc_common(char *base, long size) {
  rb_key *new_key;
  rb_info *new_info;

  if (++alloc_cur > alloc_max)
    alloc_max = alloc_cur;

  ++alloc_tot;
  if (quarantine_size > quarantine_max) {
    long quarantine_mb_tmp;
    quarantine_max = quarantine_size;
    quarantine_mb_tmp = quarantine_max/1024/1024;
    if (quarantine_mb_tmp > quarantine_max_mb) {
      quarantine_max_mb = quarantine_mb_tmp;
      printf("[interposer] quarantine_max = %ld MB\n", quarantine_max_mb);
    }
  }

  memset(base, 0, size);
  ls_clear_ptrlog(base, size);

  new_key = rb_new_key(base, base + size);
  new_info = rb_new_info(size);
  return RBTreeInsert(rb_root, new_key, new_info);
}

static void free_common(char *base, rb_red_blk_node *node) {
  rb_info *info;

  --alloc_cur;

  info = node->info;
  if (info->flags & RB_INFO_FREED)
    printf("[interposer] double free??????\n");

  if (info->refcnt <= 0) {
    free_func(base);
    RBDelete(rb_root, node);
  } else {
    info->flags |= RB_INFO_FREED;
    quarantine_size += info->size;
  }
}

void *malloc(size_t size) {
  char *ret = malloc_func(size);
  if (!ret)
    printf("[interposer] malloc failed ??????\n");
  alloc_common(ret, size);
  return(ret);
}

void *calloc(size_t num, size_t size) {
  char *ret = calloc_func(num, size);
  if (!ret)
    printf("[interposer] calloc failed ??????\n");
  alloc_common(ret, num*size);
  return(ret);
}

void *realloc(void *ptr, size_t size) {
  char *p = (char*)ptr;
  rb_red_blk_node *orig_node, *new_node;
  rb_key *orig_key, *new_key;
  rb_info *orig_info;
  char *ret;

  if (p==NULL)
    return malloc(size);

  tmp_rb_key.base = tmp_rb_key.end = p;
  orig_node = RBExactQuery(rb_root, &tmp_rb_key);

  orig_key = orig_node->key;
  if (orig_key->base != p)
    printf("[interposer] ptr != base in realloc ??????\n");
  if ((p+size) <= orig_key->end)
    return p;

  /* just malloc */
  ret = malloc_func(size);
  if (!ret)
    printf("[interposer] malloc failed ??????\n");

  new_node = alloc_common(ret, size);

  orig_info = orig_node->info;
  memcpy(ret, p, orig_info->size);

  new_key = new_node->key;
  ls_copy_ptrlog(new_key->base, orig_key->base, orig_info->size);

  free_common(p, orig_node);

  return(ret);
}

void free(void *ptr) {
  rb_red_blk_node *node;
  rb_info *info;

  if (ptr==NULL)
    return;

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

  info = node->info;
  ls_dec_ptrlog(ptr, info->size);
  free_common(ptr, node);
}
