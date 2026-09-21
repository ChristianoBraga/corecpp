// Core C++ example, UD V. A non virtual method called through a base pointer
// runs the method of the base, a virtual one runs the override of the class
// tag. Core C++ forbids redefining a non virtual method, so the two
// resolutions coincide on every accepted program. Exit code 21.
class Base {
public:
  int fixed() { return 1; }
  virtual int dispatched() { return 10; }
};

class Derived : public Base {
public:
  int dispatched() override { return 20; }
};

int main() {
  Base* b = new Derived();
  return b->fixed() + b->dispatched();
}
