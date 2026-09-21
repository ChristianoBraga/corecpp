// Core C++ example, functions. Naive recursion, about 250 thousand calls for
// fib(25) = 75025. Exit code 75025 mod 256 = 17. Used to compare the running
// time of the interpreter with a compiled binary.
int fib(int n) {
  return n < 2 ? n : fib(n - 1) + fib(n - 2);
}

int main() {
  return fib(25);
}
