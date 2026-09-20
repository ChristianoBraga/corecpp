// Core C++ example, UD III. A local reference is a second name for the same
// location, so the write through y is read through x. Exit code 42.
int main() {
  int x = 1;
  int& y = x;
  y = y + 41;
  return x;
}
