// Core C++ example, UD VII. The case study of Lecture 29 in the imperative
// fragment. The sum of the even numbers from 1 to n, with an accumulator and
// a loop. State is a variable, abstraction is a function. Exit code 30.
int sumEven(int n) {
  int acc = 0;
  for (int i = 1; i <= n; i = i + 1) {
    if (i % 2 == 0) { acc = acc + i; }
  }
  return acc;
}

int main() { return sumEven(10); }
