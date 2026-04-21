#include <stdio.h>

struct node {
  int elt;
  struct node* next;
};

// reachability in linked lists
/*@ inductive reachable{L}(struct list *root, struct list *to) {
  @ case empty{L}: \forall struct list *l; reachable(l,l) ;
  @ case non_empty{L}: \forall struct list *l1,*l2;
  @ \valid(l1) && reachable(l1->next,l2) ==> reachable(l1,l2) ;
  @ }
*/

/*@ requires \true;
  @ ensures \true;
  @ assigns *l1
  @*/
void append(struct node *l1, struct node *l2) {
  if (l1 -> next == NULL)
    l1 -> next = l1;
  else
    append(l1->next, l2);
}
