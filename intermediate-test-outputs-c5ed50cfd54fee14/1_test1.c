// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__720
} Unit__716;

// FUNCTIONS


static Unit__716 uni__718(int x__694, int y__695) {
  printf("%s\n", (x__694 == y__695) ? "True" : "False");
  return Unit__720;
}


static Unit__716 uni__721(bool x__694, bool y__695) {
  printf("%s\n", (x__694 == y__695) ? "True" : "False");
  return Unit__720;
}

// MAIN


int main() {
  Unit__716 n__696 = uni__718(1, 4);
  Unit__716 m__697 = uni__721(true, false);
  (void) n__696;
  printf("()\n");
  (void) m__697;
  printf("()\n");
  (void) uni__721(true, true);
  printf("()\n");
}

