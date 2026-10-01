// Core C++ example, std::function. A field of type std::function compares
// with nullptr, which tells whether it has a target, and is called once it
// has one. Exit code 9.
#include <functional>
class Button {
public:
  std::function<int()> onClick;
  int press() {
    if (this->onClick == nullptr) { return 0; }
    std::function<int()> f = this->onClick;
    return f();
  }
};
int main() {
  Button* b = new Button();
  int before = b->press();
  std::function<int()> nine = [=]() -> int { return 9; };
  b->onClick = nine;
  return before + b->press();
}
