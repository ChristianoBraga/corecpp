// Core C++ example, UD IV. A reference parameter may be bound to a field or to
// a vector element, because both denote locations. Exit code 21.
class P {
public:
  int a;
};

void inc(int& r) {
  r = r + 1;
}

int main() {
  P* p = new P();
  inc(p->a);
  inc(p->a);
  std::vector<int>* v = new std::vector<int>(2);
  inc((*v)[1]);
  return p->a * 10 + (*v)[1];
}
