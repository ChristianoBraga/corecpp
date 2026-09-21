// Core C++ example, UD VI. auto copies the type of the initialiser, which
// may be a pointer to an instantiation. No rule of the type checker is new,
// the initialiser simply has a type auto can copy. Returns 12.
template<typename T>
class Caixa {
private:
  T valor;
public:
  Caixa(T v) { this->valor = v; }
  T abre() { return valor; }
};

int main() {
  auto c = new Caixa<int>(12);
  auto n = c->abre();
  delete c;
  return n;
}
