// Core C++ example, delete and destructors. A second delete of the same object is error in Core
// C++, exit code 134, and undefined behaviour in C++, where g++ may abort,
// crash or exit normally. The exit codes differ by design.
class Box {
public:
  int v;
};

int main() {
  Box* c = new Box();
  c->v = 1;
  delete c;
  delete c;
  return 0;
}
