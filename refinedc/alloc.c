#include <stddef.h>

typedef struct
  [[rc::refined_by("l : {list Z}")]]
  [[rc::typedef("list_t : {maybe2 cons l} @ optionalO<λ (ty, l). &own<...>, null>")]]
list_node {
  [[rc::field("int<i32>")]]
  int val;
  [[rc::field("l @ list_t")]]
  struct list_node *next;
} *list_t;

[[rc::parameters("p : loc", "q : loc", "xs : {list Z}")]]
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
