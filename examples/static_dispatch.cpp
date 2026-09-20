// Core C++ example, UD V. A non virtual method called through a base pointer
// runs the method of the base, a virtual one runs the override of the class
// tag. Core C++ forbids redefining a non virtual method, so the two
// resolutions coincide on every accepted program. Exit code 21.
class Base {
public:
  int fixo() { return 1; }
  virtual int variavel() { return 10; }
};

class Derivada : public Base {
public:
  int variavel() override { return 20; }
};

int main() {
  Base* b = new Derivada();
  return b->fixo() + b->variavel();
}
