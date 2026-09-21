// Core C++ example, UD III. The two calls write through the same pointer, and
// the value of the sum depends on which call runs first. Core C++ evaluates the
// left operand first, so the result is 1 + 10 * 2 = 21. C++17 leaves the order
// of the operands of + unspecified, and g++ may compute 2 + 10 * 1 = 12.
// Exit code 21 in Core C++.
class Cell {
public:
  int n;
};

int next(Cell* c) {
  c->n = c->n + 1;
  return c->n;
}

int main() {
  Cell* c = new Cell();
  return next(c) + 10 * next(c);
}
