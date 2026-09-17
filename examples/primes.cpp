// Core C++ example, UD III. Counts the primes below 20000 by trial division,
// about 2.2 million loop iterations. There are 2262 of them, exit code
// 2262 mod 256 = 214.
bool prime(int n) {
  if (n < 2) { return false; }
  int d = 2;
  while (d * d <= n) {
    if (n % d == 0) { return false; }
    d = d + 1;
  }
  return true;
}

int main() {
  int count = 0;
  for (int i = 0; i < 20000; i = i + 1) {
    if (prime(i)) { count = count + 1; }
  }
  return count;
}
