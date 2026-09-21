// Core C++ example, references. The reference lives in the inner block and the
// variable it names lives outside it. At the closing brace the binding y
// disappears and the location of x stays in the store. Exit code 6.
int main() {
  int x = 1;
  {
    int& y = x;
    y = 5;
  }
  return x + 1;
}
