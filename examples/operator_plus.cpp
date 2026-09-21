// Core C++ example, UD VI. An operator overloaded as a member. The infix
// *a + *b is the call of Ponto::operator+, with the left operand as the
// receiver. The result is a pointer, because objects are never copied.
// Returns 10.
class Ponto {
public:
  int x;
  int y;
  Ponto* operator+(Ponto& o) {
    Ponto* r = new Ponto();
    r->x = x + o.x;
    r->y = y + o.y;
    return r;
  }
};

int main() {
  Ponto* a = new Ponto();
  a->x = 1;
  a->y = 4;
  Ponto* b = new Ponto();
  b->x = 2;
  b->y = 3;
  Ponto* c = *a + *b;
  int r = c->x + c->y;
  delete a;
  delete b;
  delete c;
  return r;
}
