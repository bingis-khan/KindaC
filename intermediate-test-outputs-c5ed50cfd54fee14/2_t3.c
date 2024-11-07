// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef 
struct {
  int (*cFun1__880__1)(int);
} Fun__878;


static Fun__878 Fun1__880f(int (*cFun1__880__1)(int)) {
  return (Fun__878) { .cFun1__880__1 = cFun1__880__1 };
}

// FUNCTIONS


static int lambda__881(int x__857) {
  return (x__857 + 1);
}

// MAIN


int main() {
  Fun__878 x__858 = Fun1__880f(lambda__881);
  (void) x__858;
  printf("Fun\n");
}

