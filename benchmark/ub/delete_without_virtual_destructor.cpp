// Core C++ benchmark, undefined behaviour. A delete through a pointer to a base class with no virtual destructor (N4659 §8.3.5 ¶3).
class Base {
public:
  int x;
  ~Base() { x = 0; }
};

class Derived : public Base {
public:
  int y;
};

int main() {
  Base* b = new Derived();
  b->x = 3;
  delete b;
  return 3;
}
