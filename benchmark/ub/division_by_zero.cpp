// Core C++ benchmark, undefined behaviour. A division by zero (N4659 §8.6 ¶4).
int quot(int a, int b) { return a / b; }

int main() {
  int s = 0;
  for (int i = 3; i >= 0; i = i - 1) {
    s = s + quot(12, i);
  }
  return s;
}
