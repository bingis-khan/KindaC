// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES

// FUNCTIONS



struct et1012 {
  int n__1002;
};


static int lambda__1042f(struct et1012* env) {
  return env->n__1002;
}



struct ut1013 {
  int (*fun)(void*);
  
  
  union {
    struct et1012 e1012;
  } uni;
};



struct et1015 {
  int n__1002;
};


static struct ut1013 lambda__1043f(struct et1015* env) {
  return (struct ut1013) { .fun = (int (*)(void*)) lambda__1042f, .uni.e1012 = { .n__1002 = env->n__1002 } };
}



struct ut1016 {
  struct ut1013 (*fun)(void*);
  
  
  union {
    struct et1015 e1015;
  } uni;
};



struct et1018 {
  int n__1002;
};


static struct ut1016 lambda__1044f(struct et1018* env) {
  return (struct ut1016) { .fun = (struct ut1013 (*)(void*)) lambda__1043f, .uni.e1015 = { .n__1002 = env->n__1002 } };
}



struct ut1019 {
  struct ut1016 (*fun)(void*);
  
  
  union {
    struct et1018 e1018;
  } uni;
};



struct et1021 {
  int n__1002;
};


static struct ut1019 lambda__1045f(struct et1021* env) {
  return (struct ut1019) { .fun = (struct ut1016 (*)(void*)) lambda__1044f, .uni.e1018 = { .n__1002 = env->n__1002 } };
}



struct ut1022 {
  struct ut1019 (*fun)(void*);
  
  
  union {
    struct et1021 e1021;
  } uni;
};



struct et1024 {
  int n__1002;
};


static struct ut1022 lambda__1046f(struct et1024* env) {
  return (struct ut1022) { .fun = (struct ut1019 (*)(void*)) lambda__1045f, .uni.e1021 = { .n__1002 = env->n__1002 } };
}



struct ut1025 {
  struct ut1022 (*fun)(void*);
  
  
  union {
    struct et1024 e1024;
  } uni;
};



struct et1027 {
  int n__1002;
};


static struct ut1025 lambda__1047f(struct et1027* env) {
  return (struct ut1025) { .fun = (struct ut1022 (*)(void*)) lambda__1046f, .uni.e1024 = { .n__1002 = env->n__1002 } };
}



struct ut1028 {
  struct ut1025 (*fun)(void*);
  
  
  union {
    struct et1027 e1027;
  } uni;
};



struct et1030 {
  int n__1002;
};


static struct ut1028 lambda__1048f(struct et1030* env) {
  return (struct ut1028) { .fun = (struct ut1025 (*)(void*)) lambda__1047f, .uni.e1027 = { .n__1002 = env->n__1002 } };
}



struct ut1031 {
  struct ut1028 (*fun)(void*);
  
  
  union {
    struct et1030 e1030;
  } uni;
};



struct et1033 {
  int n__1002;
};


static struct ut1031 lambda__1049f(struct et1033* env) {
  return (struct ut1031) { .fun = (struct ut1028 (*)(void*)) lambda__1048f, .uni.e1030 = { .n__1002 = env->n__1002 } };
}



struct ut1034 {
  struct ut1031 (*fun)(void*);
  
  
  union {
    struct et1033 e1033;
  } uni;
};



struct et1036 {
  int n__1002;
};


static struct ut1034 lambda__1050f(struct et1036* env) {
  return (struct ut1034) { .fun = (struct ut1031 (*)(void*)) lambda__1049f, .uni.e1033 = { .n__1002 = env->n__1002 } };
}



struct ut1037 {
  struct ut1034 (*fun)(void*);
  
  
  union {
    struct et1036 e1036;
  } uni;
};



struct et1039 {
  int n__1002;
};


static struct ut1037 lambda__1051f(struct et1039* env) {
  return (struct ut1037) { .fun = (struct ut1034 (*)(void*)) lambda__1050f, .uni.e1036 = { .n__1002 = env->n__1002 } };
}

// MAIN



struct ut1040 {
  struct ut1037 (*fun)(void*);
  
  
  union {
    struct et1039 e1039;
  } uni;
};


int main() {
  int n__1002 = 123;
  struct ut1040 lam__1003 = (struct ut1040) { .fun = (struct ut1037 (*)(void*)) lambda__1051f, .uni.e1039 = { .n__1002 = n__1002 } };
  printf("() -> () -> () -> () -> () -> () -> () -> () -> () -> () -> Int at %p\n", (void*) lam__1003.fun);
}

