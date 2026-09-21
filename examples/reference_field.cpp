// Core C++ example, references. A reference to a field and a reference to a vector
// element alias locations inside objects, and the writes through them are seen
// through the object. Exit code 79.
class P {
public:
  int a;
  int b;
};

int main() {
  P* p = new P();
  int& a = p->a;
  a = 7;
  std::vector<int>* v = new std::vector<int>(3);
  int& e = (*v)[1];
  e = 9;
  return p->a * 10 + (*v)[1];
}
