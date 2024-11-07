// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES

// FUNCTIONS


static int id__747(int x__725) {
  return x__725;
}



struct et740 {
  int (*id__747)(int);
};


static int f__748f(struct et740* env, int x__727) {
  env->id__747(x__727);
  return 1;
}

// MAIN



struct ut745 {
  int (*fun)(void*, int);
  
  
  union {
    struct et740 e740;
  } uni;
};


int main() {
  struct ut745 f__748 = (struct ut745) { .fun = (int (*)(void*, int)) f__748f, .uni.e740 = { .id__747 = id__747 } };
  struct ut745 temp0 = f__748;
  printf("%d\n", temp0.fun(&temp0.uni, 1));
}

