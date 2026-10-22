// Core C++ example, closures. The lambda captures the pointer c by copy, and the
#include <functional>
// object it points to outlives the block of counter, so each call updates the
// same counter. The result is 2 + 3 + 1. Exit code 6.
class Box {
public:
  int value;
};

std::function<int()>* counter() {
  Box* c = new Box();
  c->value = 0;
  return new std::function<int()>([=]() -> int { c->value = c->value + 1; return c->value; });
}

int main() {
  std::function<int()>* k = counter();
  int first = (*k)();
  return (*k)() + (*k)() + first;
}
