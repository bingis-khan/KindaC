// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__558
} Unit__556;

// FUNCTIONS



struct et539 {
  int n__527;
};


static Unit__556 printn__557f(struct et539* env) {
  printf("%d\n", env->n__527);
  return Unit__558;
}



struct ut544 {
  Unit__556 (*fun)(void*);
  
  
  union {
    struct et539 e539;
  } uni;
};



struct et543 {
  struct ut544 printn__557;
};


static Unit__556 printn2__559f(struct et543* env) {
  printf("%d\n", 2);
  struct ut544 temp0 = env->printn__557;
  temp0.fun(&temp0.uni);
  return Unit__558;
}



struct ut549 {
  Unit__556 (*fun)(void*);
  
  
  union {
    struct et543 e543;
  } uni;
};



struct et548 {
  struct ut549 printn2__559;
};


static Unit__556 printn3__560f(struct et548* env) {
  printf("%d\n", 3);
  struct ut549 temp1 = env->printn2__559;
  temp1.fun(&temp1.uni);
  return Unit__558;
}

// MAIN



struct ut554 {
  Unit__556 (*fun)(void*);
  
  
  union {
    struct et548 e548;
  } uni;
};


int main() {
  int n__527 = 69;
  struct ut544 printn__557 = (struct ut544) { .fun = (Unit__556 (*)(void*)) printn__557f, .uni.e539 = { .n__527 = n__527 } };
  struct ut549 printn2__559 = (struct ut549) { .fun = (Unit__556 (*)(void*)) printn2__559f, .uni.e543 = { .printn__557 = printn__557 } };
  struct ut554 printn3__560 = (struct ut554) { .fun = (Unit__556 (*)(void*)) printn3__560f, .uni.e548 = { .printn2__559 = printn2__559 } };
  struct ut554 temp2 = printn3__560;
  temp2.fun(&temp2.uni);
}

