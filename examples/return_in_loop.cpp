// Core C++ example, UD III. A return inside a loop interrupts the loop, the
// block and the function. Exit code 7.
int main() {
  int i = 0;
  while (true) {
    i = i + 1;
    if (i == 7) {
      return i;
    }
  }
}
