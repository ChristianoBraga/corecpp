// Core C++ example, UD V. Single inheritance, a virtual method redefined with
// override, subsumption of Quadrado* to Forma*, dispatch by the class tag of
// the object, and a namespace. The virtual destructor lets delete through the
// base pointer reach the object. Exit code 16.
namespace Geometria {
  class Forma {
  public:
    virtual int area() { return 0; }
    virtual ~Forma() { }
  };
  class Quadrado : public Forma {
  private:
    int lado;
  public:
    Quadrado(int l) { this->lado = l; }
    int area() override { return lado * lado; }
  };
}

int main() {
  Geometria::Forma* f = new Geometria::Quadrado(4);
  int a = f->area();
  delete f;
  return a;
}
