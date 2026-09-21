// Core C++ example, UD VII. The case study of Lecture 29 in the object
// oriented fragment. The accumulator is the state of an object, and the
// filter is a virtual method the derived class redefines, so the criterion
// is chosen by dispatch and not by a parameter. Exit code 30.
class Adder {
public:
  int acc;
  virtual bool accepts(int i) { return true; }
  void add(int i) { if (accepts(i)) { acc = acc + i; } }
  int total() { return acc; }
  virtual ~Adder() { }
};

class EvenAdder : public Adder {
public:
  bool accepts(int i) override { return i % 2 == 0; }
};

int main() {
  Adder* s = new EvenAdder();
  for (int i = 1; i <= 10; i = i + 1) { s->add(i); }
  int r = s->total();
  delete s;
  return r;
}
