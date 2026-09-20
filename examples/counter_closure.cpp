// Core C++ example, UD IV. The lambda captures the pointer c by copy, and the
// object it points to outlives the block of contador, so each call updates the
// same counter. The result is 2 + 3 + 1. Exit code 6.
class Caixa {
public:
  int valor;
};

std::function<int()> contador() {
  Caixa* c = new Caixa();
  c->valor = 0;
  return [=]() -> int { c->valor = c->valor + 1; return c->valor; };
}

int main() {
  std::function<int()> k = contador();
  int primeiro = k();
  return k() + k() + primeiro;
}
