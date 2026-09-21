// Core C++ example, abstract data types. A stack over a vector. The
// public section is the signature, the private section the representation,
// reachable only from the methods of the class. Exit code 42.
class Stack {
private:
  std::vector<int>* items;
  int top;
public:
  Stack(int n) { this->items = new std::vector<int>(n); this->top = 0; }
  void push(int x) { (*items)[top] = x; top = top + 1; }
  int pop() { top = top - 1; return (*items)[top]; }
  bool empty() { return top == 0; }
};

int main() {
  Stack* p = new Stack(8);
  p->push(1);
  p->push(41);
  int a = p->pop();
  int b = p->pop();
  if (p->empty()) { return a + b; }
  return 0;
}
