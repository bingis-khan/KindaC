// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__77
} Unit__75;

// FUNCTIONS



struct et61 {
  int y__49;
  int x__48;
};


static int f__73f(struct et61* env, int z__51, bool n__52) {
  printf("%s\n", n__52 ? "True" : "False");
  return ((env->x__48 + env->y__49) + z__51);
}


static int f__76f(struct et61* env, int z__51, Unit__75 n__52) {
  (void) n__52;
  printf("()\n");
  return ((env->x__48 + env->y__49) + z__51);
}


static int f__78f(struct et61* env, int z__51, int n__52) {
  printf("%d\n", n__52);
  return ((env->x__48 + env->y__49) + z__51);
}

// MAIN



struct ut70 {
  int (*fun)(void*, int, int);
  
  
  union {
    struct et61 e61;
  } uni;
};



struct ut69 {
  int (*fun)(void*, int, Unit__75);
  
  
  union {
    struct et61 e61;
  } uni;
};



struct ut68 {
  int (*fun)(void*, int, bool);
  
  
  union {
    struct et61 e61;
  } uni;
};


int main() {
  int x__48 = 1;
  int y__49 = 2;
  struct ut70 f__78 = (struct ut70) { .fun = (int (*)(void*, int, int)) f__78f, .uni.e61 = { .y__49 = y__49, .x__48 = x__48 } };
  struct ut69 f__76 = (struct ut69) { .fun = (int (*)(void*, int, Unit__75)) f__76f, .uni.e61 = { .y__49 = y__49, .x__48 = x__48 } };
  struct ut68 f__73 = (struct ut68) { .fun = (int (*)(void*, int, bool)) f__73f, .uni.e61 = { .y__49 = y__49, .x__48 = x__48 } };
  struct ut68 temp0 = f__73;
  printf("%d\n", temp0.fun(&temp0.uni, 69, true));
  struct ut69 temp1 = f__76;
  printf("%d\n", temp1.fun(&temp1.uni, 420, Unit__77));
  printf("(Int, Int) -> Int at %p\n", (void*) f__78.fun);
}

