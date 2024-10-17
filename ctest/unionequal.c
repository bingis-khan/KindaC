
typedef union {
  int x;
  double y;
} Huh;

int main() {
  Huh a, b;
  a.x = 69;
  b.y = 123.456;

  (void) (a == b);
}
