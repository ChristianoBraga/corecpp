// Core C++ example, UD VI. An operator overloaded as a member. The infix
// *a + *b is the call of Point::operator+, with the left operand as the
// receiver. The result is a pointer, because objects are never copied.
// Returns 10.
class Point {
public:
  int x;
  int y;
  Point* operator+(Point& o) {
    Point* r = new Point();
    r->x = x + o.x;
    r->y = y + o.y;
    return r;
  }
};

int main() {
  Point* a = new Point();
  a->x = 1;
  a->y = 4;
  Point* b = new Point();
  b->x = 2;
  b->y = 3;
  Point* c = *a + *b;
  int r = c->x + c->y;
  delete a;
  delete b;
  delete c;
  return r;
}
