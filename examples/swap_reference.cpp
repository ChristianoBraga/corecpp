// Core C++ example, UD IV. Reference parameters alias the arguments, so the
// swap inside troca is visible in main. Exit code 21.
void troca(int& a, int& b) {
  int t = a;
  a = b;
  b = t;
}

int main() {
  int x = 1;
  int y = 2;
  troca(x, y);
  return x * 10 + y;
}
