// Core C++ example, UD V. delete through a base pointer with a virtual
// destructor runs the destructor of the derived class and then the one of
// the base, each recording itself in a shared object. Exit code 11.
class Record {
public:
  int n;
};

class Base {
public:
  Record* r;
  virtual ~Base() { r->n = r->n + 1; }
};

class Derived : public Base {
public:
  ~Derived() { r->n = r->n + 10; }
};

int main() {
  Record* rec = new Record();
  Derived* d = new Derived();
  d->r = rec;
  Base* b = d;
  delete b;
  return rec->n;
}
