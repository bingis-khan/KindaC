// includes

#include<stdio.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef 
struct {
  int (*cFun__64__1)(int);
} Fun__60;


static Fun__60 Fun__64f(int (*cFun__64__1)(int)) {
  return (Fun__60) { .cFun__64__1 = cFun__64__1 };
}



typedef enum {
  Unit__68
} Unit__67;

// FUNCTIONS


static int id__65(int x__23) {
  return x__23;
}


static int add1__66(int x__25) {
  return (x__25 + 1);
}


static Unit__67 uni__69(Fun__60 x__27, Fun__60 y__28) {
  return Unit__68;
}

// MAIN


int main(){
  // pass (nuttin)
  // pass (nuttin)
  // pass (nuttin)
  // pass (nuttin)
  // pass (nuttin)
  // pass (nuttin)
  Fun__60 x__29 = Fun__64f(id__65);
  Fun__60 y__30 = Fun__64f(add1__66);
  (void) uni__69(x__29, y__30);
  printf("()\n");
  (void) x__29;
  printf("Fun\n");
}

