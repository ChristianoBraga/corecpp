// Core C++ benchmark, undefined behaviour. Flowing off the end of a function other than main that returns int (N4659 §9.6.3 ¶2).
int sign(int x) {
  if (x > 0) {
    return 1;
  }
  if (x < 0) {
    return 2;
  }
}

int main() {
  return sign(0);
}
