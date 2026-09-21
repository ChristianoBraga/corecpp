// Core C++ example, UD VII. The case study of Lecture 29 in the object
// oriented fragment. The accumulator is the state of an object, and the
// filter is a virtual method the derived class redefines, so the criterion
// is chosen by dispatch and not by a parameter. Exit code 30.
class Somador {
public:
  int acc;
  virtual bool aceita(int i) { return true; }
  void junta(int i) { if (aceita(i)) { acc = acc + i; } }
  int total() { return acc; }
  virtual ~Somador() { }
};

class SomadorPar : public Somador {
public:
  bool aceita(int i) override { return i % 2 == 0; }
};

int main() {
  Somador* s = new SomadorPar();
  for (int i = 1; i <= 10; i = i + 1) { s->junta(i); }
  int r = s->total();
  delete s;
  return r;
}
