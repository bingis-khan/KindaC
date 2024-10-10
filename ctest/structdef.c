#include <stdio.h>

struct A {
  int x;
  int y;
};


int main() {
  struct A s = (struct A) { 1, 2 };
  struct A sp = (struct A) { .x = 1, .y = 2 };
  printf("%d %d\n", s.x, s.y);
}
