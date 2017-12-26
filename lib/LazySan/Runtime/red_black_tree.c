#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "red_black_tree.h"

extern void* (*malloc_func)(size_t size);
extern void (*free_func)(void *ptr);
#define malloc malloc_func
#define free free_func

rb_red_blk_tree *rb_root = NULL;

void __attribute__((constructor)) init_rb_tree() {
  rb_root = RBTreeCreate();
}

int RBTreeCompare(const rb_red_blk_node *a, const rb_red_blk_node *b) {
  if ((a->base <= b->base)
      && (b->base <= a->end)) {
    if ((b->base != b->end)
        && !((a->end < b->base) || (b->end < a->base)))
      printf("[interposer] existing entry with overlaping region!\n");
    return 0;
  }
  if( a->base > b->base) return(1);
  if( a->base < b->base) return(-1);
  return(0);
}

rb_red_blk_tree* RBTreeCreate() {
  rb_red_blk_tree* newTree;
  rb_red_blk_node* temp;

  newTree=(rb_red_blk_tree*) malloc(sizeof(rb_red_blk_tree));

  /*  see the comment in the rb_red_blk_tree structure in red_black_tree.h */
  /*  for information on nil and root */
  temp=newTree->nil= (rb_red_blk_node*) malloc(sizeof(rb_red_blk_node));
  temp->parent=temp->left=temp->right=temp;
  temp->red=0;
  temp=newTree->root= (rb_red_blk_node*) malloc(sizeof(rb_red_blk_node));
  temp->parent=temp->left=temp->right=newTree->nil;
  temp->red=0;
  return(newTree);
}

void LeftRotate(rb_red_blk_tree* tree, rb_red_blk_node* x) {
  rb_red_blk_node* y;
  rb_red_blk_node* nil=tree->nil;

  /*  I originally wrote this function to use the sentinel for */
  /*  nil to avoid checking for nil.  However this introduces a */
  /*  very subtle bug because sometimes this function modifies */
  /*  the parent pointer of nil.  This can be a problem if a */
  /*  function which calls LeftRotate also uses the nil sentinel */
  /*  and expects the nil sentinel's parent pointer to be unchanged */
  /*  after calling this function.  For example, when RBDeleteFixUP */
  /*  calls LeftRotate it expects the parent pointer of nil to be */
  /*  unchanged. */

  y=x->right;
  x->right=y->left;

  if (y->left != nil) y->left->parent=x; /* used to use sentinel here */
  /* and do an unconditional assignment instead of testing for nil */

  y->parent=x->parent;

  /* instead of checking if x->parent is the root as in the book, we */
  /* count on the root sentinel to implicitly take care of this case */
  if( x == x->parent->left) {
    x->parent->left=y;
  } else {
    x->parent->right=y;
  }
  y->left=x;
  x->parent=y;

#ifdef DEBUG_ASSERT
  assert(!tree->nil->red && "nil not red in LeftRotate");
#endif
}

void RightRotate(rb_red_blk_tree* tree, rb_red_blk_node* y) {
  rb_red_blk_node* x;
  rb_red_blk_node* nil=tree->nil;

  /*  I originally wrote this function to use the sentinel for */
  /*  nil to avoid checking for nil.  However this introduces a */
  /*  very subtle bug because sometimes this function modifies */
  /*  the parent pointer of nil.  This can be a problem if a */
  /*  function which calls LeftRotate also uses the nil sentinel */
  /*  and expects the nil sentinel's parent pointer to be unchanged */
  /*  after calling this function.  For example, when RBDeleteFixUP */
  /*  calls LeftRotate it expects the parent pointer of nil to be */
  /*  unchanged. */

  x=y->left;
  y->left=x->right;

  if (nil != x->right)  x->right->parent=y; /*used to use sentinel here */
  /* and do an unconditional assignment instead of testing for nil */

  /* instead of checking if x->parent is the root as in the book, we */
  /* count on the root sentinel to implicitly take care of this case */
  x->parent=y->parent;
  if( y == y->parent->left) {
    y->parent->left=x;
  } else {
    y->parent->right=x;
  }
  x->right=y;
  y->parent=x;

#ifdef DEBUG_ASSERT
  assert(!tree->nil->red && "nil not red in RightRotate");
#endif
}

void TreeInsertHelp(rb_red_blk_tree* tree, rb_red_blk_node* z) {
  /*  This function should only be called by InsertRBTree (see above) */
  rb_red_blk_node* x;
  rb_red_blk_node* y;
  rb_red_blk_node* nil=tree->nil;

  z->left=z->right=nil;
  y=tree->root;
  x=tree->root->left;
  while( x != nil) {
    y=x;
    if (1 == RBTreeCompare(x,z)) {
      x=x->left;
    } else {
      x=x->right;
    }
  }
  z->parent=y;
  if ( (y == tree->root) ||
       (1 == RBTreeCompare(y,z))) {
    y->left=z;
  } else {
    y->right=z;
  }

#ifdef DEBUG_ASSERT
  assert(!tree->nil->red && "nil not red in TreeInsertHelp");
#endif
}

rb_red_blk_node * RBTreeInsert(rb_red_blk_tree* tree, char* base, long size) {
  rb_red_blk_node * y;
  rb_red_blk_node * x;
  rb_red_blk_node * newNode;

  x=(rb_red_blk_node*) malloc(sizeof(rb_red_blk_node));
  x->base=base;
  x->end=base+size;
  x->size=size;
  x->refcnt=REFCNT_INIT;
  x->flags=0;

  TreeInsertHelp(tree,x);
  newNode=x;
  x->red=1;
  while(x->parent->red) { /* use sentinel instead of checking for root */
    if (x->parent == x->parent->parent->left) {
      y=x->parent->parent->right;
      if (y->red) {
	x->parent->red=0;
	y->red=0;
	x->parent->parent->red=1;
	x=x->parent->parent;
      } else {
	if (x == x->parent->right) {
	  x=x->parent;
	  LeftRotate(tree,x);
	}
	x->parent->red=0;
	x->parent->parent->red=1;
	RightRotate(tree,x->parent->parent);
      }
    } else { /* case for x->parent == x->parent->parent->right */
      y=x->parent->parent->left;
      if (y->red) {
	x->parent->red=0;
	y->red=0;
	x->parent->parent->red=1;
	x=x->parent->parent;
      } else {
	if (x == x->parent->left) {
	  x=x->parent;
	  RightRotate(tree,x);
	}
	x->parent->red=0;
	x->parent->parent->red=1;
	LeftRotate(tree,x->parent->parent);
      }
    }
  }
  tree->root->left->red=0;
  return(newNode);

#ifdef DEBUG_ASSERT
  assert(!tree->nil->red && "nil not red in RBTreeInsert");
  assert(!tree->root->red && "root not red in RBTreeInsert");
#endif
}

rb_red_blk_node* TreeSuccessor(rb_red_blk_tree* tree,rb_red_blk_node* x) {
  rb_red_blk_node* y;
  rb_red_blk_node* nil=tree->nil;
  rb_red_blk_node* root=tree->root;

  if (nil != (y = x->right)) { /* assignment to y is intentional */
    while(y->left != nil) { /* returns the minium of the right subtree of x */
      y=y->left;
    }
    return(y);
  } else {
    y=x->parent;
    while(x == y->right) { /* sentinel used instead of checking for nil */
      x=y;
      y=y->parent;
    }
    if (y == root) return(nil);
    return(y);
  }
}

void InorderTreePrint(rb_red_blk_tree* tree, rb_red_blk_node* x, int depth) {
  if (x != tree->nil) {
    int i = depth;
    InorderTreePrint(tree,x->left,depth+1);
    while (i--) printf(" ");
    printf("[0x%lx, 0x%lx]", (long)x->base, (long)x->end);
    printf("(0x%lx, %ld)#%d%s\n",
           x->size, x->size, x->refcnt, (x->flags & RB_INFO_FREED) ? "F" : "");
    InorderTreePrint(tree,x->right,depth+1);
  }
}

void TreeDestHelper(rb_red_blk_tree* tree, rb_red_blk_node* x) {
  rb_red_blk_node* nil=tree->nil;
  if (x != nil) {
    TreeDestHelper(tree,x->left);
    TreeDestHelper(tree,x->right);
    free(x);
  }
}

void RBTreeDestroy(rb_red_blk_tree* tree) {
  TreeDestHelper(tree,tree->root->left);
  free(tree->root);
  free(tree->nil);
  free(tree);
}

void RBTreePrint(rb_red_blk_tree* tree) {
  InorderTreePrint(tree,tree->root->left,0);
}

rb_red_blk_node* RBExactQuery(rb_red_blk_tree* tree, char* p) {
  rb_red_blk_node* x=tree->root->left;
  rb_red_blk_node* nil=tree->nil;
  rb_red_blk_node tmp = {0};
  int compVal;
  tmp.base = tmp.end = p;
  if (x == nil) return(0);
  compVal=RBTreeCompare(x,&tmp);
  while(0 != compVal) {/*assignemnt*/
    if (1 == compVal) { /* x->key > q */
      x=x->left;
    } else {
      x=x->right;
    }
    if ( x == nil) return(0);
    compVal=RBTreeCompare(x,&tmp);
  }
  return(x);
}

void RBDeleteFixUp(rb_red_blk_tree* tree, rb_red_blk_node* x) {
  rb_red_blk_node* root=tree->root->left;
  rb_red_blk_node* w;

  while( (!x->red) && (root != x)) {
    if (x == x->parent->left) {
      w=x->parent->right;
      if (w->red) {
	w->red=0;
	x->parent->red=1;
	LeftRotate(tree,x->parent);
	w=x->parent->right;
      }
      if ( (!w->right->red) && (!w->left->red) ) {
	w->red=1;
	x=x->parent;
      } else {
	if (!w->right->red) {
	  w->left->red=0;
	  w->red=1;
	  RightRotate(tree,w);
	  w=x->parent->right;
	}
	w->red=x->parent->red;
	x->parent->red=0;
	w->right->red=0;
	LeftRotate(tree,x->parent);
	x=root; /* this is to exit while loop */
      }
    } else { /* the code below is has left and right switched from above */
      w=x->parent->left;
      if (w->red) {
	w->red=0;
	x->parent->red=1;
	RightRotate(tree,x->parent);
	w=x->parent->left;
      }
      if ( (!w->right->red) && (!w->left->red) ) {
	w->red=1;
	x=x->parent;
      } else {
	if (!w->left->red) {
	  w->right->red=0;
	  w->red=1;
	  LeftRotate(tree,w);
	  w=x->parent->left;
	}
	w->red=x->parent->red;
	x->parent->red=0;
	w->left->red=0;
	RightRotate(tree,x->parent);
	x=root; /* this is to exit while loop */
      }
    }
  }
  x->red=0;

#ifdef DEBUG_ASSERT
  assert(!tree->nil->red && "nil not black in RBDeleteFixUp");
#endif
}

void RBDelete(rb_red_blk_tree* tree, rb_red_blk_node* z){
  rb_red_blk_node* y;
  rb_red_blk_node* x;
  rb_red_blk_node* nil=tree->nil;
  rb_red_blk_node* root=tree->root;

  y= ((z->left == nil) || (z->right == nil)) ? z : TreeSuccessor(tree,z);
  x= (y->left == nil) ? y->right : y->left;
  if (root == (x->parent = y->parent)) { /* assignment of y->p to x->p is intentional */
    root->left=x;
  } else {
    if (y == y->parent->left) {
      y->parent->left=x;
    } else {
      y->parent->right=x;
    }
  }
  if (y != z) { /* y should not be nil in this case */

#ifdef DEBUG_ASSERT
    assert( (y!=tree->nil) && "y is nil in RBDelete\n");
#endif
    /* y is the node to splice out and x is its child */

    if (!(y->red)) RBDeleteFixUp(tree,x);

    y->left=z->left;
    y->right=z->right;
    y->parent=z->parent;
    y->red=z->red;
    z->left->parent=z->right->parent=y;
    if (z == z->parent->left) {
      z->parent->left=y;
    } else {
      z->parent->right=y;
    }
    free(z);
  } else {
    if (!(y->red)) RBDeleteFixUp(tree,x);
    free(y);
  }

#ifdef DEBUG_ASSERT
  assert(!tree->nil->red && "nil not black in RBDelete");
#endif
}
