// Core C++ example, commands and functions. Exit code 120.
int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) {
    acc = acc * i;
  }
  return acc;
}

int main() {
  return factorial(5);
}
