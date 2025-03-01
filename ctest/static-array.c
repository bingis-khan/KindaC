#include <stdio.h>


typedef struct {
  int arr[3];
} Array20;

int main() {
  Array20 arr = (Array20) { .arr = { 1, 2, 3 } };
  printf("dupsko %d %d %d\n", arr.arr[0], arr.arr[1], arr.arr[2]);
}
