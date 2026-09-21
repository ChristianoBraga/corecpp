// Core C++ example, UD IV. A lambda passed directly as the argument of a
// std::function parameter, applied twice. Exit code 81.
int applyTwice(std::function<int(int)> f, int x) {
  return f(f(x));
}

int main() {
  return applyTwice([=](int x) -> int { return x * x; }, 3);
}
