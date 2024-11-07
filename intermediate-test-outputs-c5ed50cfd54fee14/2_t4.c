// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__923
} Unit__921;



typedef struct{
  
  
  enum {
    Fun1__919t, Fun2__922t
  } tag;
  
  
  union {
    
    
    struct {
      int (*cFun1__919__1)(int);
    } Fun1__919;
    
    
    struct {
      Unit__921 (*cFun2__922__1)();
    } Fun2__922;
  } uni;
} Fun__917;


static Fun__917 Fun1__919f(int (*cFun1__919__1)(int)) {
  return (Fun__917) { .tag = Fun1__919t,  .uni.Fun1__919 = { .cFun1__919__1 = cFun1__919__1 } };
}


static Fun__917 Fun2__922f(Unit__921 (*cFun2__922__1)()) {
  return (Fun__917) { .tag = Fun2__922t,  .uni.Fun2__922 = { .cFun2__922__1 = cFun2__922__1 } };
}

// FUNCTIONS


static int lambda__920(int x__885) {
  return (x__885 + 1);
}


static Unit__921 lambda__924() {
  return Unit__923;
}

// MAIN


int main() {
  Fun__917 x__886 = Fun1__919f(lambda__920);
  (void) x__886;
  printf("Fun\n");
  Fun__917 y__887 = Fun2__922f(lambda__924);
  (void) y__887;
  printf("Fun\n");
}

