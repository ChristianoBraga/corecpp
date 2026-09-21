// Core C++ example, UD VII. The functional fragment. Expressions, recursion
// in place of iteration, lambdas and function values, and no assignment, no
// loop and no heap. Every location is written once, at its declaration, so an
// expression has the same value every time it is evaluated. Exit code 30.
int soma(int n) {
  return n == 0 ? 0 : n + soma(n - 1);
}

std::function<int(int)> escala(int k) {
  return [=](int x) -> int { return k * x; };
}

int aplica(std::function<int(int)> f, int v) {
  return f(v);
}

int main() {
  std::function<int(int)> triplo = escala(3);
  int s = soma(4);
  return aplica(triplo, s);
}
