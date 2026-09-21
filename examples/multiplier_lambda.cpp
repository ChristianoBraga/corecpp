// Core C++ example, closures. A function returns a lambda that captured k by copy,
// and apply calls it through a std::function parameter. Exit code 42.
std::function<int(int)> multiplier(int k) {
  return [=](int x) -> int { return k * x; };
}

int apply(std::function<int(int)> f, int v) {
  return f(v);
}

int main() {
  return apply(multiplier(3), 14);
}
