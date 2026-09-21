// Core C++ example, the functional fragment. The functional fragment. Expressions, recursion
// in place of iteration, lambdas and function values, and no assignment, no
// loop and no heap. Every location is written once, at its declaration, so an
// expression has the same value every time it is evaluated. Exit code 30.
int sum(int n) {
  return n == 0 ? 0 : n + sum(n - 1);
}

std::function<int(int)> scale(int k) {
  return [=](int x) -> int { return k * x; };
}

int apply(std::function<int(int)> f, int v) {
  return f(v);
}

int main() {
  std::function<int(int)> triple = scale(3);
  int s = sum(4);
  return apply(triple, s);
}
