// Core C++ example, UD II. In Core C++ the division is error. In C++ it is
// undefined behaviour, and on most machines the process is killed by SIGFPE.
int main() {
  int z = 0;
  return 10 / z;
}
