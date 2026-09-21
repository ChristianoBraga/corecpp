// Core C++ example, UD IV. Reference parameters alias the arguments, so the
// swap inside swap is visible in main. Exit code 21.
void swap(int& a, int& b) {
  int t = a;
  a = b;
  b = t;
}

int main() {
  int x = 1;
  int y = 2;
  swap(x, y);
  return x * 10 + y;
}
