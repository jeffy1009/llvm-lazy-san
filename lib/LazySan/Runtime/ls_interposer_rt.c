#define _GNU_SOURCE
#include <stdio.h>
#include <dlfcn.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <sys/mman.h>
#include <errno.h>
#include "red_black_tree.h"

long *global_ptrlog;
extern rb_red_blk_tree *rb_root;

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

/*****************************/
/**  Refcnt modification  ****/
/*****************************/

/* p - written pointer value
   dest - store destination */
void ls_inc_refcnt(char *p, char *dest) {
  rb_red_blk_node *n;
  long offset, widx, bidx;

  if (!p)
    return;

  num_ptrs++;
  n = RBExactQuery(rb_root, p);
  if (n) {
    if ((n->flags & RB_INFO_FREED) && n->refcnt == REFCNT_INIT)
      printf("[interposer] refcnt became alive again??\n");
    ++n->refcnt;
  }

  /* mark pointer type field */
  offset = (long)dest >> 3;
  widx = offset >> 6; /* word index */
  bidx = offset & 0x3F; /* bit index */
  global_ptrlog[widx] |= (1UL << bidx);
}

void ls_dec_refcnt(char *p, char *dummy) {
  rb_red_blk_node *n;

  if (!p)
    return;

  n = RBExactQuery(rb_root, p);
  if (n) { /* is heap node */
    if (n->refcnt<=REFCNT_INIT && !(n->flags & RB_INFO_RCBELOWZERO)) {
      n->flags |= RB_INFO_RCBELOWZERO;
      printf("[interposer] refcnt <= 0???\n");
    }
    --n->refcnt;
    if (n->refcnt<=0) {
      if (n->flags & RB_INFO_FREED) { /* marked to be freed */
        quarantine_size -= n->size;
        free_func(n->base);
        RBDelete(rb_root, n);
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

  return RBTreeInsert(rb_root, base, size);
}

static void free_common(char *base, rb_red_blk_node *n) {
  --alloc_cur;

  if (n->flags & RB_INFO_FREED)
    printf("[interposer] double free??????\n");

  if (n->refcnt <= 0) {
    free_func(base);
    RBDelete(rb_root, n);
  } else {
    n->flags |= RB_INFO_FREED;
    quarantine_size += n->size;
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
  rb_red_blk_node *orig_n, *new_n;
  char *ret;

  if (p==NULL)
    return malloc(size);

  orig_n = RBExactQuery(rb_root, p);

  if (orig_n->base != p)
    printf("[interposer] ptr != base in realloc ??????\n");
  if ((p+size) <= orig_n->end)
    return p;

  /* just malloc */
  ret = malloc_func(size);
  if (!ret)
    printf("[interposer] malloc failed ??????\n");

  new_n = alloc_common(ret, size);

  memcpy(ret, p, orig_n->size);

  ls_copy_ptrlog(new_n->base, orig_n->base, orig_n->size);

  free_common(p, orig_n);

  return(ret);
}

void free(void *ptr) {
  rb_red_blk_node *n;

  if (ptr==NULL)
    return;

  n = RBExactQuery(rb_root, ptr);
  if (!n) {
    /* there are no dangling pointers to this node,
       so the node is already removed from the rangetree */
    /* NOTE: there can be a dangling pointer in the register
       and that register value could later be stored in memory.
       Should we handle this case?? */
    free_func(ptr);
    return;
  }

  ls_dec_ptrlog(ptr, n->size);
  free_common(ptr, n);
}
