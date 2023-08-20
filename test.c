#include <stdbool.h>
#include <stdio.h>







static int lam23 () { return 69; }
static int lam24 (int loc13, int loc14) { return loc13+loc14; }
static bool lam25 (bool loc16) { return loc16; }
static int lam27 (bool loc19) { return 1; }
static int (bool) lam26 (int loc18) { return lam27; }
static int (bool) (int) lam28 (int (bool) (*loc21)(int)) { return loc21; }
int main ( ) {
    int (*loc12)() = lam23;
    int (*loc15)(int,int) = lam24;
    bool (*loc17)(bool) = lam25;
    int (bool) (*loc20)(int) = lam26;
    int (bool) (int) (*loc22)(int (bool) (int)) = lam28;
    printf("%d\n", loc20(1)(true));
    printf("%x: (1) (2) 1\n", loc22(loc20));
    printf("%x: () 1\n", loc12);
    printf("%x: (1,  1) 1\n", loc15);
    printf("%d\n", loc12());
    printf("%d\n", loc15(1, 2));
    printf("%x: (2) 2\n", loc17);
    printf("%s\n", loc17(true) ? "True" : "False");
}