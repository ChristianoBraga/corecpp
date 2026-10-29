// Core C++ benchmark, not a Core C++ program. The increment operator ++.
int main() {
  int s = 0;
  for (int i = 0; i < 4; ++i) {
    s = s + i;
  }
  return s;
}
