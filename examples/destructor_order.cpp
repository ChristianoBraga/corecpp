// Core C++ example, UD V. delete through a base pointer with a virtual
// destructor runs the destructor of the derived class and then the one of
// the base, each recording itself in a shared object. Exit code 11.
class Registro {
public:
  int n;
};

class Base {
public:
  Registro* r;
  virtual ~Base() { r->n = r->n + 1; }
};

class Derivada : public Base {
public:
  ~Derivada() { r->n = r->n + 10; }
};

int main() {
  Registro* reg = new Registro();
  Derivada* d = new Derivada();
  d->r = reg;
  Base* b = d;
  delete b;
  return reg->n;
}
