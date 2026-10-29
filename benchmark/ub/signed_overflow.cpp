// Core C++ benchmark, undefined behaviour. A signed overflow, a result outside the range of int (N4659 §8 ¶4).
int main() {
  int x = 1;
  for (int i = 0; i < 31; i = i + 1) {
    x = x * 2;
  }
  return x % 256;
}
