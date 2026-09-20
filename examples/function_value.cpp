// Core C++ example, UD IV. A function value is copied into another variable and
// called through it. Exit code 7.
int main() {
  std::function<int(int, int)> g = [=](int a, int b) -> int { return a - b; };
  std::function<int(int, int)> h = g;
  return h(10, 3);
}
