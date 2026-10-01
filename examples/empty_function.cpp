// Core C++ example, std::function. A field of type std::function starts with no
// target, the value nullptr gives it, and calling it is error in Core C++. In
// C++ the call throws std::bad_function_call, which, uncaught, aborts the
// process. Exit code 134 in both.
#include <functional>
class Button {
public:
  std::function<int()> onClick;
};
int main() {
  Button* b = new Button();
  std::function<int()> f = b->onClick;
  return f();
}
