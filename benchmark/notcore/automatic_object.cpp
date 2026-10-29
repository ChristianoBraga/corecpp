// Core C++ benchmark, not a Core C++ program. An object of class type with automatic storage duration, created without new.
class Box {
public:
  int v;
};

int main() {
  Box b;
  b.v = 4;
  return b.v;
}
