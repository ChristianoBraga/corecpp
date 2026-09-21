// Core C++ example, the type checker. Rejected by the Core C++ type checker, because bool
// and int do not mix and there are no implicit conversions. g++ accepts it,
// converts true to 1 and exits with 2. This is a program C++ accepts and Core
// C++ does not, the direction the subset allows.
int main() {
  bool b = true;
  int x = b + 1;
  return x;
}
