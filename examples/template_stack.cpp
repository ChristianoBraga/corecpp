// Core C++ example, class templates. A class template instantiated at two types. Each
// instantiation is a class of its own, built by substitution before the
// program is checked, and the two share no subtype relation. Returns 7.
template<typename T>
class Stack {
private:
  std::vector<T>* items;
  int top;
public:
  Stack(int n) {
    this->items = new std::vector<T>(n);
    this->top = 0;
  }
  void push(T x) {
    (*items)[top] = x;
    top = top + 1;
  }
  T pop() {
    top = top - 1;
    return (*items)[top];
  }
  ~Stack() { delete items; }
};

class Point {
public:
  int x;
};

int main() {
  Stack<int>* p = new Stack<int>(4);
  p->push(3);
  p->push(4);
  int s = p->pop() + p->pop();

  Stack<Point*>* q = new Stack<Point*>(2);
  Point* a = new Point();
  a->x = 0;
  q->push(a);
  Point* b = q->pop();
  int r = s + b->x;
  delete a;
  delete p;
  delete q;
  return r;
}
