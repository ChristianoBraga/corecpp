// Core C++ example, UD III. The right operand of an assignment is evaluated
// before the left one, as C++17 fixes. Exit code 42.
int main() {
  int x = 1;
  x = x + 41;
  return x;
}
