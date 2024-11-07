// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES

// FUNCTIONS


static int id__380(int n__322) {
  return n__322;
}


static int id2__381(int n__325) {
  return n__325;
}


static int (*id__382(int (*n__322)(int)))(int) {
  return n__322;
}

// MAIN


int main() {
  int (*f__323)(int) = id__380;
  printf("%d\n", f__323(123));
  printf("%d\n", f__323(69));
  printf("%d\n", f__323(f__323(f__323(f__323(f__323(((1 + 2) + 3)))))));
  printf("%d\n", id2__381(123));
  printf("%d\n", id2__381(69));
  printf("%d\n", id2__381(id2__381(id2__381(id2__381(id2__381(((1 + 2) + 3)))))));
  printf("%d\n", id__382(id2__381)(123));
}

