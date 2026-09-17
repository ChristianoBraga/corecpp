import CoreCpp

open CoreCpp

/-! ## Lexer and parser -/

#eval lex "int x = 10; // comment\nx = x + 1;"

#eval parseExpr "1 + 2 * 3"
#eval parseExpr "a < b && !(c == d) ? x : y"
#eval parseExpr "f(1, g(2), -3)"
#eval parseExpr "1 +"

#eval parseStatement "if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }"
#eval parseStatement "for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }"
#eval parseStatement "int x;"

#eval parseProgram "int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) {
    acc = acc * i;
  }
  return acc;
}

int main() {
  int x = 5;
  while (x > 0) {
    if (x % 2 == 0) { x = x / 2; } else { x = x - 1; }
  }
  auto y = factorial(4);
  return y;
}"

/-! ## Evaluator -/

def prog (s : String) : Except String (Except Error Val) :=
  (parseProgram s).map run

#eval prog "int factorial(int n) {
  int acc = 1;
  for (int i = 2; i <= n; i = i + 1) { acc = acc * i; }
  return acc;
}
int main() { return factorial(5); }"

-- scope, the inner block variable does not shadow the outer one after the block
#eval prog "int main() {
  int x = 1;
  { int x = 10; x = x + 1; }
  return x;
}"

-- return inside while interrupts the loop
#eval prog "int main() {
  int i = 0;
  while (true) { i = i + 1; if (i == 7) { return i; } }
}"

-- int overflow is an error
#eval prog "int main() { int x = 2147483647; return x + 1; }"

-- division by zero is an error
#eval prog "int main() { int z = 0; return 10 / z; }"

-- division truncates toward zero, as in C++
#eval prog "int main() { return -7 / 2 * 10 + -7 % 2; }"

-- short circuit avoids the division
#eval prog "int main() { int z = 0; bool b = z != 0 && 10 / z > 1; return b ? 1 : 0; }"

-- void function without return
#eval prog "void nothing() { int x = 1; } int main() { nothing(); return 3; }"

-- assignment evaluates the right operand before the left
#eval prog "int main() { int x = 1; x = x + 41; return x; }"

-- type checking
#eval (parseProgram "int main() { bool b = true; int x = b + 1; return x; }").map check
#eval (parseProgram "int f(int n) { return n; } int main() { return f(true); }").map check
#eval (parseProgram "int main() { int x = 1; return x; }").map check

-- derivation trace of a small program
#eval do
  let p ← parseProgram "int main() { int x = 1; x = x + 41; return x; }"
  let (r, log) := runWith true p
  return (r, renderTrace log)
