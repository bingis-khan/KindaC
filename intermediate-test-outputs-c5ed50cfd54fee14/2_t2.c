// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef 
struct {
  int (*cFun__850__1)(int);
} Fun__848;


static Fun__848 Fun__850f(int (*cFun__850__1)(int)) {
  return (Fun__848) { .cFun__850__1 = cFun__850__1 };
}

// FUNCTIONS


static int id__851(int x__816) {
  return x__816;
}


static int add1__852(int x__818) {
  return (x__818 + 1);
}

// MAIN


int main() {
  Fun__848 x__819 = Fun__850f(id__851);
  Fun__848 y__820 = Fun__850f(add1__852);
  Fun__848 temp0 = x__819;
  Fun__848 temp1 = y__820;
  printf("%s\n", (0 ==  memcmp(&temp0, &temp1, sizeof(Fun__848))) ? "True" : "False");
}

