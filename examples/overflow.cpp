// Core C++ example, UD II. In Core C++ the sum overflows and the result is
// error. In C++ signed overflow is undefined behaviour, and g++ may print
// anything, typically the wrapped value -2147483648 as exit code 0.
int main() {
  int x = 2147483647;
  return x + 1;
}
