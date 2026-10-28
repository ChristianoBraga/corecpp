// Core C++ example, a class template inside a namespace. The type parameter T
// belongs to the template declaration, not to the namespace (N4659 §6.3.9
// paragraph 2), so Store::Box<int> substitutes int for T. Exit code 7.
namespace Store {
  template<typename T>
  class Box {
  public:
    T item;
  };
}

int main() {
  Store::Box<int>* b = new Store::Box<int>();
  b->item = 7;
  int r = b->item;
  delete b;
  return r;
}
