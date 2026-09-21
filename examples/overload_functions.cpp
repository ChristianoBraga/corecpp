// Core C++ example, UD VI. Overloading by the type of the arguments. The two
// declarations of dobro are one overload set, and each call selects the
// candidate that accepts its argument. Returns 46.
int dobro(int n) { return 2 * n; }

bool dobro(bool b) { return b; }

int dobro(int a, int b) { return 2 * (a + b); }

int main() {
  int x = dobro(21);
  int y = dobro(1, 1);
  return dobro(false) ? 0 : x + y;
}
