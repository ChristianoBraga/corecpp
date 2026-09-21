// Core C++ example, UD VII. The imperative fragment. Basic types, variables,
// assignment, a local reference, the loops and first order functions, and
// nothing that reaches the heap. Every value in the store is basic, and the
// store grows by declaration and shrinks at scope exit. Exit code 49.
int gcd(int a, int b) {
  while (b != 0) {
    int t = b;
    b = a % b;
    a = t;
  }
  return a;
}

int power(int base, int e) {
  int acc = 1;
  for (int i = 0; i < e; i = i + 1) {
    acc = acc * base;
  }
  return acc;
}

int main() {
  int x = gcd(48, 18);
  int& y = x;
  y = y + 1;
  return power(y, 2);
}
