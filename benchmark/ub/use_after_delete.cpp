// Core C++ benchmark, undefined behaviour. An indirection through an invalid pointer value after delete (N4659 §6.7 ¶4).
class Box {
public:
  int v;
};

int main() {
  Box* b = new Box();
  b->v = 5;
  delete b;
  return b->v;
}
