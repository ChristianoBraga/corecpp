// Core C++ example, a chain of overrides. Shape declares area virtual, Square
// overrides it, and Cube overrides it again. The override in Square is
// virtual without the word virtual, as in C++17, so a call through a Shape*
// and one through a Square* both reach the method of Cube. Exit code 66.
class Shape {
public:
  virtual int area() { return 1; }
};
class Square : public Shape {
public:
  int area() override { return 4; }
};
class Cube : public Square {
public:
  int area() override { return 6; }
};

int main() {
  Shape* s = new Cube();
  Square* q = new Cube();
  return s->area() * 10 + q->area();
}
