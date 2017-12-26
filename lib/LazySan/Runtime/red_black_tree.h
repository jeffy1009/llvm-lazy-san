#ifdef DMALLOC
#include <dmalloc.h>
#endif

/* comment out the line below to remove all the debugging assertion */
/* checks from the compiled code.  */
/* #define DEBUG_ASSERT 1 */

#define REFCNT_INIT 0

#define RB_INFO_FREED 		0x1
#define RB_INFO_RCBELOWZERO 	0x10000

typedef struct rb_red_blk_node {
  char *base, *end;
  long size;
  int refcnt;
  int flags;
  int red; /* if red=0 then the node is black */
  struct rb_red_blk_node* left;
  struct rb_red_blk_node* right;
  struct rb_red_blk_node* parent;
} rb_red_blk_node;


typedef struct rb_red_blk_tree {
  /*  A sentinel is used for root and for nil.  These sentinels are */
  /*  created when RBTreeCreate is caled.  root->left should always */
  /*  point to the node which is the root of the tree.  nil points to a */
  /*  node which should always be black but has aribtrary children and */
  /*  parent and no key or info.  The point of using these sentinels is so */
  /*  that the root and nil nodes do not require special cases in the code */
  rb_red_blk_node* root;
  rb_red_blk_node* nil;
} rb_red_blk_tree;

rb_red_blk_tree* RBTreeCreate();
rb_red_blk_node * RBTreeInsert(rb_red_blk_tree*, char*, long);
void RBTreePrint(rb_red_blk_tree*);
void RBDelete(rb_red_blk_tree* , rb_red_blk_node* );
void RBTreeDestroy(rb_red_blk_tree*);
rb_red_blk_node* RBExactQuery(rb_red_blk_tree*, char*);
