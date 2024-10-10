/*
  Demonstration of function pointers in different situations.
*/


#include <stdio.h>

int add2(int x, int y) {
  return x + y;
}

int (*retfun1())(int, int) {
  return add2;
}

int (*(*retfun2())())(int, int) {
  return retfun1;
}

int takeThing(int (*f)(int, int)) {
  return f(5, 8);
}

int takeThing2(int (*(*f)())(int, int)) {
  return f()(5, 8);
}

int main() {
  int (*(*(*f)())())(int, int) = retfun2;
  int (*g)(int, int) = add2;
  int (*h)(int (*)(int, int)) = takeThing;
  int (*i)(int (*(*)())(int, int)) = takeThing2;
  printf("%d\n", f()()(1, 2));
  printf("%d\n", g(1, 2));
  printf("%d\n", h(add2));
  printf("%d\n", takeThing2(retfun1));
}
