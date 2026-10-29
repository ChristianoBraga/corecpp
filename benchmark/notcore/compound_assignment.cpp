// Core C++ benchmark, not a Core C++ program. The compound assignment +=.
int main() {
  int s = 0;
  for (int i = 0; i < 5; i = i + 1) {
    s += i;
  }
  return s;
}
