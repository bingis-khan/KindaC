// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__1000
} Unit__995;



typedef 
struct {
  int (*cFun__997__1)(int);
  int cFun__997__2;
  Unit__995 (*cFun__997__3)();
  bool cFun__997__4;
  Unit__995 cFun__997__5;
} Fun__993;


static Fun__993 Fun__997f(int (*cFun__997__1)(int), int cFun__997__2, Unit__995 (*cFun__997__3)(), bool cFun__997__4, Unit__995 cFun__997__5) {
  return (Fun__993) { .cFun__997__1 = cFun__997__1, .cFun__997__2 = cFun__997__2, .cFun__997__3 = cFun__997__3, .cFun__997__4 = cFun__997__4, .cFun__997__5 = cFun__997__5 };
}

// FUNCTIONS


static int lambda__998(int x__968) {
  return (x__968 + 1);
}


static Unit__995 print1__999() {
  printf("%d\n", 1);
  return Unit__1000;
}

// MAIN


int main() {
  Fun__993 x__969 = Fun__997f(lambda__998, 420, print1__999, true, Unit__1000);
  (void) x__969;
  printf("Fun\n");
}

