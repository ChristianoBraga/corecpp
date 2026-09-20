// Core C++ example, UD II. Two pointers are equal when they denote the same
// object. A field written through one pointer is read through the other,
// because both denote the same record of locations. Exit code 17.
class Ponto {
public:
  int x;
  int y;
};

int main() {
  Ponto* a = new Ponto();
  Ponto* b = a;
  Ponto* c = new Ponto();
  b->x = 7;
  return a->x + (a == b ? 10 : 0) + (a == c ? 100 : 0);
}
