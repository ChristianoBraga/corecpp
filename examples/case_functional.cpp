// Core C++ example, the functional fragment. The same sum of the even
// numbers, with recursion in place of the loop and the filter as a function
// value passed as an argument. No location is written twice. Exit code 30.
int sumTo(std::function<bool(int)> p, int n) {
  return n == 0 ? 0 : (p(n) ? n : 0) + sumTo(p, n - 1);
}

int main() {
  std::function<bool(int)> even = [=](int i) -> bool { return i % 2 == 0; };
  return sumTo(even, 10);
}
