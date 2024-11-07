// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__440
} Unit__436;

// FUNCTIONS


static Unit__436 printx__439(int x__388) {
  printf("%d\n", x__388);
  return Unit__440;
}


static Unit__436 printx__441(Unit__436 x__388) {
  (void) x__388;
  printf("()\n");
  return Unit__440;
}



struct et406 {
  Unit__436 (*printx__439)(int);
};



struct et418 {
  Unit__436 (*printx__439)(int);
};



struct ut433 {
  Unit__436 (*fun)(void*);
  
  
  union {
    struct et406 e406;
    struct et418 e418;
  } uni;
};



struct et411 {
  Unit__436 (*printx__439)(int);
};



struct et423 {
  Unit__436 (*printx__441)(Unit__436);
};



struct ut434 {
  Unit__436 (*fun)(void*);
  
  
  union {
    struct et411 e411;
    struct et423 e423;
  } uni;
};


static Unit__436 bool__442(bool cond__384, struct ut433 ifTrue__385, struct ut434 ifFalse__386) {
  
  if (cond__384) {
    struct ut433 temp0 = ifTrue__385;
    temp0.fun(&temp0.uni);
  }
  
  else {
    struct ut434 temp1 = ifFalse__386;
    temp1.fun(&temp1.uni);
  }
  return Unit__440;
}


static Unit__436 lambda__443f(struct et406* env) {
  return env->printx__439(69);
}


static Unit__436 lambda__444f(struct et411* env) {
  return env->printx__439(420);
}


static Unit__436 lambda__445f(struct et418* env) {
  return env->printx__439(1234);
}


static Unit__436 lambda__446f(struct et423* env) {
  return env->printx__441(Unit__440);
}

// MAIN


int main() {
  bool__442((1 == 2), (struct ut433) { .fun = (Unit__436 (*)(void*)) lambda__443f, .uni.e406 = { .printx__439 = printx__439 } }, (struct ut434) { .fun = (Unit__436 (*)(void*)) lambda__444f, .uni.e411 = { .printx__439 = printx__439 } });
  Unit__436 temp2 = Unit__440;
  Unit__436 temp3 = Unit__440;
  bool__442((0 ==  memcmp(&temp2, &temp3, sizeof(Unit__436))), (struct ut433) { .fun = (Unit__436 (*)(void*)) lambda__445f, .uni.e418 = { .printx__439 = printx__439 } }, (struct ut434) { .fun = (Unit__436 (*)(void*)) lambda__446f, .uni.e423 = { .printx__441 = printx__441 } });
}

