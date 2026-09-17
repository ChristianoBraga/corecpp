// Core C++ example, UD III. The inner x shadows the outer one only inside the
// block, and its location leaves the store at the closing brace. Exit code 1.
int main() {
  int x = 1;
  {
    int x = 10;
    x = x + 1;
  }
  return x;
}
