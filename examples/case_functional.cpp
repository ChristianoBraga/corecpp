// Core C++ example, UD VII. The case study of Lecture 29 in the functional
// fragment. Recursion in place of the loop, and the filter is a function
// value passed as an argument. Node location is written twice. Exit code 30.
int sumTo(std::function<bool(int)> p, int n) {
  return n == 0 ? 0 : (p(n) ? n : 0) + sumTo(p, n - 1);
}

int main() {
  std::function<bool(int)> even = [=](int i) -> bool { return i % 2 == 0; };
  return sumTo(even, 10);
}
