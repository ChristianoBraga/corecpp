// Core C++ example, UD II. The right operand of && is not evaluated when the
// left one is false, so the division by zero never happens. Exit code 0.
int main() {
  int z = 0;
  bool b = z != 0 && 10 / z > 1;
  return b ? 1 : 0;
}
