// Core C++ example, inheritance and dispatch. Single inheritance, a virtual method redefined with
// override, subsumption of Square* to Shape*, dispatch by the class tag of
// the object, and a namespace. The virtual destructor lets delete through the
// base pointer reach the object. Exit code 16.
namespace Geometry {
  class Shape {
  public:
    virtual int area() { return 0; }
    virtual ~Shape() { }
  };
  class Square : public Shape {
  private:
    int side;
  public:
    Square(int l) { this->side = l; }
    int area() override { return side * side; }
  };
}

int main() {
  Geometry::Shape* f = new Geometry::Square(4);
  int a = f->area();
  delete f;
  return a;
}
