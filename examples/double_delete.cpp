// Core C++ example, UD V. A second delete of the same object is error in Core
// C++, exit code 134, and undefined behaviour in C++, where g++ may abort,
// crash or exit normally. The exit codes differ by design.
class Caixa {
public:
  int v;
};

int main() {
  Caixa* c = new Caixa();
  c->v = 1;
  delete c;
  delete c;
  return 0;
}
