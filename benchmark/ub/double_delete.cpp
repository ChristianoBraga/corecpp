// Core C++ benchmark, undefined behaviour. A second delete passes an invalid pointer value to the deallocation function (N4659 §6.7 ¶4).
class Box {
public:
  int v;
};

int main() {
  Box* b = new Box();
  Box* c = b;
  delete b;
  delete c;
  return 0;
}
