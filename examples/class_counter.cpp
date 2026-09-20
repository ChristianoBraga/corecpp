// Core C++ example, UD V. A class with a private field, a constructor and two
// methods. The constructor runs on new, this->valor names the field, and the
// unqualified valor inside a method is the field of this. Exit code 42.
class Contador {
private:
  int valor;
public:
  Contador(int inicial) { this->valor = inicial; }
  void incrementa() { valor = valor + 1; }
  int atual() { return valor; }
};

int main() {
  Contador* c = new Contador(40);
  c->incrementa();
  c->incrementa();
  return c->atual();
}
