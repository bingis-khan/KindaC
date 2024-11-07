// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__647
} Unit__631;



typedef enum {
  Proxy__635
} Proxy__634;



typedef enum {
  Proxy__639
} Proxy__637;



typedef enum {
  Proxy__643
} Proxy__641;

// FUNCTIONS


static Proxy__637 makeUnchecked__638() {
  return Proxy__639;
}


static Proxy__641 check__642(Proxy__637 p__594) {
  (void) p__594;
  printf("Proxy Unchecked\n");
  return Proxy__643;
}


static bool consumeChecked__645(Proxy__641 p__597) {
  return true;
}


static Unit__631 main__632() {
  Proxy__634 x__590 = Proxy__635;
  (void) x__590;
  printf("Proxy Int\n");
  printf("%d\n", 123);
  Proxy__637 uch__598 = makeUnchecked__638();
  (void) uch__598;
  printf("Proxy Unchecked\n");
  Proxy__641 ch__599 = check__642(uch__598);
  (void) ch__599;
  printf("Proxy Checked\n");
  bool ch__600 = consumeChecked__645(ch__599);
  printf("%s\n", ch__600 ? "True" : "False");
  return Unit__647;
}

// MAIN


int main() {
  main__632();
}

