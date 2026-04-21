/*@ requires \valid(n);
  @ assigns *n;
  @ ensures *n == \old (*n);
  @*/
void increment(int *n) {
  *n = *n + 1;
}
