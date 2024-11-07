// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef enum {
  Unit__690
} Unit__687;



typedef 
struct {
  int cIUseThis__692__1;
  bool cIUseThis__692__2;
} Used__691;


static Used__691 IUseThis__692f(int cIUseThis__692__1, bool cIUseThis__692__2) {
  return (Used__691) { .cIUseThis__692__1 = cIUseThis__692__1, .cIUseThis__692__2 = cIUseThis__692__2 };
}

// FUNCTIONS


static int id__684(int x__649) {
  return x__649;
}


static bool id__686(bool x__649) {
  return x__649;
}



struct et673 {
  int (*id__684)(int);
  bool (*id__686)(bool);
};


static Unit__687 g__688f(struct et673* env) {
  printf("%s\n", env->id__686(true) ? "True" : "False");
  printf("%d\n", env->id__684(1));
  return Unit__690;
}

// MAIN



struct ut676 {
  Unit__687 (*fun)(void*);
  
  
  union {
    struct et673 e673;
  } uni;
};


int main() {
  struct ut676 g__688 = (struct ut676) { .fun = (Unit__687 (*)(void*)) g__688f, .uni.e673 = { .id__684 = id__684, .id__686 = id__686 } };
  printf("() -> Unit at %p\n", (void*) g__688.fun);
  Used__691 hey__658 = IUseThis__692f(123, true);
  (void) hey__658;
  printf("Used Int\n");
  return 69;
}

