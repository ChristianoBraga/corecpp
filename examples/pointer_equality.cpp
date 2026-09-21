// Core C++ example, UD II. Two pointers are equal when they denote the same
// object. A field written through one pointer is read through the other,
// because both denote the same record of locations. Exit code 17.
class Point {
public:
  int x;
  int y;
};

int main() {
  Point* a = new Point();
  Point* b = a;
  Point* c = new Point();
  b->x = 7;
  return a->x + (a == b ? 10 : 0) + (a == c ? 100 : 0);
}
