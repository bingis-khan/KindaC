// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef 
struct {
  int (*cFun__807__1)(int);
} Fun__805;


static Fun__805 Fun__807f(int (*cFun__807__1)(int)) {
  return (Fun__805) { .cFun__807__1 = cFun__807__1 };
}



typedef enum {
  Unit__812
} Unit__810;

// FUNCTIONS


static int id__808(int x__765) {
  return x__765;
}


static int add1__809(int x__767) {
  return (x__767 + 1);
}


static Unit__810 uni__811(Fun__805 x__769, Fun__805 y__770) {
  return Unit__812;
}

// MAIN


int main() {
  Fun__805 x__771 = Fun__807f(id__808);
  Fun__805 y__772 = Fun__807f(add1__809);
  (void) uni__811(x__771, y__772);
  printf("()\n");
  (void) x__771;
  printf("Fun\n");
}

