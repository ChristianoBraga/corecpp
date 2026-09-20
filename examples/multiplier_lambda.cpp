// Core C++ example, UD IV. A function returns a lambda that captured k by copy,
// and aplica calls it through a std::function parameter. Exit code 42.
std::function<int(int)> multiplicador(int k) {
  return [=](int x) -> int { return k * x; };
}

int aplica(std::function<int(int)> f, int v) {
  return f(v);
}

int main() {
  return aplica(multiplicador(3), 14);
}
