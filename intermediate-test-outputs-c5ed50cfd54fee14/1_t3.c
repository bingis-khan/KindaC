// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__318
} Unit__316;

// FUNCTIONS



struct et297 {
  int y__283;
  int x__282;
};


static int f__314f(struct et297* env, int z__285, bool n__286) {
  printf("%s\n", n__286 ? "True" : "False");
  return ((env->x__282 + env->y__283) + z__285);
}


static int f__317f(struct et297* env, int z__285, Unit__316 n__286) {
  (void) n__286;
  printf("()\n");
  return ((env->x__282 + env->y__283) + z__285);
}


static int f__319f(struct et297* env, int z__285, int n__286) {
  printf("%d\n", n__286);
  return ((env->x__282 + env->y__283) + z__285);
}


static Unit__316 id__320(Unit__316 n__288) {
  return n__288;
}

// MAIN



struct ut310 {
  int (*fun)(void*, int, int);
  
  
  union {
    struct et297 e297;
  } uni;
};



struct ut309 {
  int (*fun)(void*, int, Unit__316);
  
  
  union {
    struct et297 e297;
  } uni;
};



struct ut308 {
  int (*fun)(void*, int, bool);
  
  
  union {
    struct et297 e297;
  } uni;
};


int main() {
  int x__282 = 1;
  int y__283 = 2;
  struct ut310 f__319 = (struct ut310) { .fun = (int (*)(void*, int, int)) f__319f, .uni.e297 = { .y__283 = y__283, .x__282 = x__282 } };
  struct ut309 f__317 = (struct ut309) { .fun = (int (*)(void*, int, Unit__316)) f__317f, .uni.e297 = { .y__283 = y__283, .x__282 = x__282 } };
  struct ut308 f__314 = (struct ut308) { .fun = (int (*)(void*, int, bool)) f__314f, .uni.e297 = { .y__283 = y__283, .x__282 = x__282 } };
  struct ut308 temp0 = f__314;
  printf("%d\n", temp0.fun(&temp0.uni, 69, true));
  struct ut309 temp1 = f__317;
  printf("%d\n", temp1.fun(&temp1.uni, 420, Unit__318));
  printf("(Int, Int) -> Int at %p\n", (void*) f__319.fun);
  printf("Unit -> Unit at %p\n", (void*) id__320);
}

