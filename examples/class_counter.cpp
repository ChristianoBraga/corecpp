// Core C++ example, UD V. A class with a private field, a constructor and two
// methods. The constructor runs on new, this->value names the field, and the
// unqualified value inside a method is the field of this. Exit code 42.
class Counter {
private:
  int value;
public:
  Counter(int initial) { this->value = initial; }
  void increment() { value = value + 1; }
  int current() { return value; }
};

int main() {
  Counter* c = new Counter(40);
  c->increment();
  c->increment();
  return c->current();
}
