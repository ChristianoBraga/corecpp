// Core C++ example, UD VI. A class template instantiated at two types. Each
// instantiation is a class of its own, built by substitution before the
// program is checked, and the two share no subtype relation. Returns 7.
template<typename T>
class Pilha {
private:
  std::vector<T>* itens;
  int topo;
public:
  Pilha(int n) {
    this->itens = new std::vector<T>(n);
    this->topo = 0;
  }
  void empilha(T x) {
    (*itens)[topo] = x;
    topo = topo + 1;
  }
  T desempilha() {
    topo = topo - 1;
    return (*itens)[topo];
  }
  ~Pilha() { delete itens; }
};

class Ponto {
public:
  int x;
};

int main() {
  Pilha<int>* p = new Pilha<int>(4);
  p->empilha(3);
  p->empilha(4);
  int s = p->desempilha() + p->desempilha();

  Pilha<Ponto*>* q = new Pilha<Ponto*>(2);
  Ponto* a = new Ponto();
  a->x = 0;
  q->empilha(a);
  Ponto* b = q->desempilha();
  int r = s + b->x;
  delete a;
  delete p;
  delete q;
  return r;
}
