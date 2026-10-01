// Core C++ example, expressions. In Core C++ the division is error. In C++ it is
// undefined behaviour, and on most machines the process is killed by SIGFPE.
// Exit code 134 in Core C++.
int main() {
  int z = 0;
  return 10 / z;
}
