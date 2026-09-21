// Core C++ example, UD II. new C() gives every field its default value, 0 for
// int, false for bool and nullptr for pointers, as C++ value initialisation
// does with the empty parentheses. Exit code 101.
class Rec {
public:
  int n;
  bool ok;
  Rec* next;
};

int main() {
  Rec* r = new Rec();
  return r->n + (r->ok ? 10 : 1) + (r->next == nullptr ? 100 : 0);
}
