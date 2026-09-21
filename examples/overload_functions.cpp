// Core C++ example, UD VI. Overloading by the type of the arguments. The two
// declarations of twice are one overload set, and each call selects the
// candidate that accepts its argument. Returns 46.
int twice(int n) { return 2 * n; }

bool twice(bool b) { return b; }

int twice(int a, int b) { return 2 * (a + b); }

int main() {
  int x = twice(21);
  int y = twice(1, 1);
  return twice(false) ? 0 : x + y;
}
