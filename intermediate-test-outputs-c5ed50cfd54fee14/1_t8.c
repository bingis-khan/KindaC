// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__585
} Unit__582;

// FUNCTIONS


static Unit__582 fun__584(int (*f__562)(int)) {
  printf("Int -> Int at %p\n", (void*) f__562);
  return Unit__585;
}


static int id__586(int x__564) {
  return x__564;
}

// MAIN


int main() {
  fun__584(id__586);
}

