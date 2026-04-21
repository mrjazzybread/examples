#include <stdio.h>

typedef struct
  [[rc::refined_by("xs : {list Z}")]]
  [[rc::typedef("list_t : {xs <> []} @ optional<&own<...>, null>")]]
  [[rc::exists("y : Z", "ys : {list Z}")]]
  [[rc::constraints("{xs = y :: ys}")]]
list_node {
  [[rc::field("y @ int<i32>")]]
  int val;
  [[rc::field("ys @ list_t")]]
  struct list_node *next;
} *list_t;

[[rc::parameters("p : loc", "xs : {list Z}", "ys : {list Z}")]]
[[rc::args("p @ &own<xs @ list_t>", "ys @ list_t")]]
[[rc::ensures("own p : {xs ++ ys} @ list_t")]]
void append(list_t *l, list_t k) {
  if(*l == NULL) {
    *l = k;
  } else {
    append(&(*l)->next, k);
  }
}

[[rc::parameters("p : loc", "n : nat")]]
[[rc::requires("{n < max_int i32}")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::ensures("own p : {n + 1} @ int<i32>")]]
void incr(int *p) {
  *p = *p + 1;
}
