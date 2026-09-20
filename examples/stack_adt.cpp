// Core C++ example, UD V. An abstract data type, a stack over a vector. The
// public section is the signature, the private section the representation,
// reachable only from the methods of the class. Exit code 42.
class Pilha {
private:
  std::vector<int>* itens;
  int topo;
public:
  Pilha(int n) { this->itens = new std::vector<int>(n); this->topo = 0; }
  void empilha(int x) { (*itens)[topo] = x; topo = topo + 1; }
  int desempilha() { topo = topo - 1; return (*itens)[topo]; }
  bool vazia() { return topo == 0; }
};

int main() {
  Pilha* p = new Pilha(8);
  p->empilha(1);
  p->empilha(41);
  int a = p->desempilha();
  int b = p->desempilha();
  if (p->vazia()) { return a + b; }
  return 0;
}
