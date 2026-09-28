// Nested conditionals, #ifndef and a #define under a condition.
#ifndef CCPP_SMALL
#define CCPP_BIG
#endif
int scale(int n) {
#ifdef CCPP_BIG
  #ifdef CCPP_DOUBLE
  return n * 20;
  #else
  return n * 10;
  #endif
#else
  return n;
#endif
}
int main() {
  return scale(3);
}
