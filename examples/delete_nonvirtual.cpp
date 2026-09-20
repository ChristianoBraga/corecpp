// Core C++ example, UD V. delete through a Base* of a Derivada object whose
// base has no virtual destructor is error in Core C++, exit code 134, and
// undefined behaviour in C++, where g++ runs only the destructor of Base and
// exits with 1. The exit codes differ by design.
class Base {
public:
  int x;
  ~Base() { x = 0; }
};

class Derivada : public Base {
public:
  int y;
};

int main() {
  Base* b = new Derivada();
  delete b;
  return 1;
}
