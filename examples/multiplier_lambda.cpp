// Core C++ example, closures. A function returns a std::function holding a lambda
#include <functional>
// that captured k by copy, and apply calls it through its pointer. Exit code 42.
std::function<int(int)>* multiplier(int k) {
  return new std::function<int(int)>([=](int x) -> int { return k * x; });
}

int apply(std::function<int(int)>* f, int v) {
  return (*f)(v);
}

int main() {
  return apply(multiplier(3), 14);
}
