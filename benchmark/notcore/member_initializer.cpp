// Core C++ benchmark, not a Core C++ program. A constructor with a member initializer list.
class Point {
public:
  int x;
  int y;
  Point(int a, int b) : x(a), y(b) {}
};

int main() {
  Point* p = new Point(2, 5);
  int s = p->x + p->y;
  delete p;
  return s;
}
