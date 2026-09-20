// Core C++ example, UD II. Dereferencing nullptr is error in Core C++. In C++
// it is undefined behaviour, and on most machines the process is killed by
// SIGSEGV. Exit code 134 in Core C++.
class No {
public:
  int valor;
  No* prox;
};

int main() {
  No* p = nullptr;
  return p->valor;
}
