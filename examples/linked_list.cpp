// Core C++ example, UD II. A class with fields only, a pointer to it as the
// recursive type, nullptr as the end of the list, and a recursive sum through
// the pointers. Every object is created with new and reached through a
// pointer. Exit code 6.
class No {
public:
  int valor;
  No* prox;
};

int soma(No* p) {
  return p == nullptr ? 0 : p->valor + soma(p->prox);
}

int main() {
  No* lista = new No();
  lista->valor = 1;
  lista->prox = new No();
  lista->prox->valor = 2;
  lista->prox->prox = new No();
  lista->prox->prox->valor = 3;
  return soma(lista);
}
