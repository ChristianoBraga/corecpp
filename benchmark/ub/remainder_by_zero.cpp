// Core C++ benchmark, undefined behaviour. A remainder by zero (N4659 §8.6 ¶4).
int main() {
  int n = 7;
  int d = n - 7;
  return n % d;
}
