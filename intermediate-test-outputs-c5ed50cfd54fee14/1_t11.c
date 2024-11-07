// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES

// FUNCTIONS



struct et139 {
  int x__115;
};


static int lambda__183f(struct et139* env, int y__116) {
  return (env->x__115 + y__116);
}



struct ut180 {
  int (*fun)(void*, int);
  
  
  union {
    struct et139 e139;
  } uni;
};


static struct ut180 lambda__184(int x__115) {
  return (struct ut180) { .fun = (int (*)(void*, int)) lambda__183f, .uni.e139 = { .x__115 = x__115 } };
}



struct et145 {
  int x__118;
};


static int lambda__185f(struct et145* env, int y__119) {
  return (env->x__118 - y__119);
}



struct ut177 {
  int (*fun)(void*, int);
  
  
  union {
    struct et145 e145;
  } uni;
};


static struct ut177 lambda__186(int x__118) {
  return (struct ut177) { .fun = (int (*)(void*, int)) lambda__185f, .uni.e145 = { .x__118 = x__118 } };
}



struct et151 {
  int x__121;
};


static int lambda__187f(struct et151* env, int y__122) {
  return (env->x__121 * y__122);
}



struct ut152 {
  int (*fun)(void*, int);
  
  
  union {
    struct et151 e151;
  } uni;
};


static struct ut152 lambda__188(int x__121) {
  return (struct ut152) { .fun = (int (*)(void*, int)) lambda__187f, .uni.e151 = { .x__121 = x__121 } };
}



struct et157 {
  int x__124;
};


static int lambda__189f(struct et157* env, int y__125) {
  return (env->x__124 / y__125);
}



struct ut158 {
  int (*fun)(void*, int);
  
  
  union {
    struct et157 e157;
  } uni;
};


static struct ut158 lambda__190(int x__124) {
  return (struct ut158) { .fun = (int (*)(void*, int)) lambda__189f, .uni.e157 = { .x__124 = x__124 } };
}


static int mapInt__191(struct ut180 f__129, int x__130) {
  struct ut180 temp0 = f__129;
  return temp0.fun(&temp0.uni, x__130);
}

// MAIN


int main() {
  struct ut180 (*add__117)(int) = lambda__184;
  struct ut177 (*sub__120)(int) = lambda__186;
  struct ut152 (*mul__123)(int) = lambda__188;
  struct ut158 (*div__126)(int) = lambda__190;
  struct ut180 temp1 = add__117(1);
  printf("%d\n", temp1.fun(&temp1.uni, 2));
  struct ut177 temp2 = sub__120(1337);
  printf("%d\n", temp2.fun(&temp2.uni, 123));
  struct ut180 add69__127 = add__117(69);
  printf("%d\n", mapInt__191(add69__127, 420));
}

