// Core C++ example, UD IV. The lambda captures the pointer c by copy, and the
// object it points to outlives the block of counter, so each call updates the
// same counter. The result is 2 + 3 + 1. Exit code 6.
class Box {
public:
  int value;
};

std::function<int()> counter() {
  Box* c = new Box();
  c->value = 0;
  return [=]() -> int { c->value = c->value + 1; return c->value; };
}

int main() {
  std::function<int()> k = counter();
  int first = k();
  return k() + k() + first;
}
