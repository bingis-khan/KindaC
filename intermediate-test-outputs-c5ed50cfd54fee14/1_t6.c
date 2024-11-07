// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__520
} Unit__516;

// FUNCTIONS


static Unit__516 printx__519(int x__452) {
  printf("%d\n", x__452);
  return Unit__520;
}


static Unit__516 printx__521(Unit__516 x__452) {
  (void) x__452;
  printf("()\n");
  return Unit__520;
}



struct et475 {
  Unit__516 (*printx__519)(int);
};



struct et487 {
  Unit__516 (*printx__519)(int);
};



struct ut510 {
  Unit__516 (*fun)(void*);
  
  
  union {
    struct et475 e475;
    struct et487 e487;
  } uni;
};



struct et480 {
  Unit__516 (*printx__519)(int);
};



struct et492 {
  Unit__516 (*printx__521)(Unit__516);
};



struct ut511 {
  Unit__516 (*fun)(void*);
  
  
  union {
    struct et480 e480;
    struct et492 e492;
  } uni;
};


static Unit__516 bool__522(bool cond__448, struct ut510 ifTrue__449, struct ut511 ifFalse__450) {
  
  if (cond__448) {
    struct ut510 temp0 = ifTrue__449;
    temp0.fun(&temp0.uni);
  }
  
  else {
    struct ut511 temp1 = ifFalse__450;
    temp1.fun(&temp1.uni);
  }
  return Unit__520;
}


static Unit__516 lambda__523f(struct et475* env) {
  return env->printx__519(69);
}


static Unit__516 lambda__524f(struct et480* env) {
  return env->printx__519(420);
}


static Unit__516 lambda__525f(struct et487* env) {
  return env->printx__519(1234);
}


static Unit__516 lambda__526f(struct et492* env) {
  return env->printx__521(Unit__520);
}

// MAIN


int main() {
  bool__522((1 == 2), (struct ut510) { .fun = (Unit__516 (*)(void*)) lambda__523f, .uni.e475 = { .printx__519 = printx__519 } }, (struct ut511) { .fun = (Unit__516 (*)(void*)) lambda__524f, .uni.e480 = { .printx__519 = printx__519 } });
  Unit__516 temp2 = Unit__520;
  Unit__516 temp3 = Unit__520;
  bool__522((0 ==  memcmp(&temp2, &temp3, sizeof(Unit__516))), (struct ut510) { .fun = (Unit__516 (*)(void*)) lambda__525f, .uni.e487 = { .printx__519 = printx__519 } }, (struct ut511) { .fun = (Unit__516 (*)(void*)) lambda__526f, .uni.e492 = { .printx__521 = printx__521 } });
  Unit__516 unit__453 = printx__519(123123123);
  printx__521(unit__453);
  printx__521(unit__453);
}

