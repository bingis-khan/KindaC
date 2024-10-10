#include <stdio.h>


void take_in(int n[4]) {
  for (int i = 0; i < 4; i++)
    printf("%d ", n[i]);
  printf("\n");
}

int main() {
  int a[5] = { 1, 2, 3, 4, 5 };
  take_in((int[4]){ 6, 7, 8 /* missing element not checked kek */  });
  printf("%d\n", a[3]);
}
