#include <stdio.h>


struct Env {
  int x;
};

struct Union {
  int (*fun)(void*, int);
  union {
    struct Env env;
  } uni;
};

int add(struct Env *env, int p) {
  return env->x + p;
}

int main() {
  int x = 69;
  struct Union u = (struct Union){ .fun = (int (*)(void*, int)) add, .uni.env = (struct Env){ .x = x } };

  printf("%d\n", u.fun(&u.uni.env, 42));
  return 0;
}
