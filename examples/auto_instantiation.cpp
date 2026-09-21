// Core C++ example, type inference. auto copies the type of the initialiser, which
// may be a pointer to an instantiation. Node rule of the type checker is new,
// the initialiser simply has a type auto can copy. Returns 12.
template<typename T>
class Box {
private:
  T value;
public:
  Box(T v) { this->value = v; }
  T get() { return value; }
};

int main() {
  auto c = new Box<int>(12);
  auto n = c->get();
  delete c;
  return n;
}
