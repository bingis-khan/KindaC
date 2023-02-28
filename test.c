#include <stdbool.h>
#include <stdio.h>






static int g8br_t1_t1_t1_ret_t1 (int loc21, int loc22, int loc23) {
    return 1;
}


static int (int, int, int) g9br_t1_t1_ret_br_t1_t1_t1_ret_t1 (int loc24, int loc25) {
    return g8br_t1_t1_t1_ret_t1;
}


static int (int, int, int) (int, int) g10br_t1_ret_br_t1_t1_ret_br_t1_t1_t1_ret_t1 (int loc26) {
    return g9br_t1_t1_ret_br_t1_t1_t1_ret_t1;
}

static int lam28 () { return 69; }
static int lam29 (int loc16, int loc17) { return loc16+loc17; }
static bool lam30 (bool loc19) { return loc19; }
int main ( ) {
    int (*loc15)() = lam28;
    int (*loc18)(int,int) = lam29;
    bool (*loc20)(bool) = lam30;
    int loc27 = g10br_t1_ret_br_t1_t1_ret_br_t1_t1_t1_ret_t1(1)(1, 2)(1, 2, 3);
    printf("%d\n", loc27);
    printf("%x: () 1\n", loc15);
    printf("%x: (1,  1) 1\n", loc18);
    printf("%d\n", loc15());
    printf("%d\n", loc18(1, 2));
    printf("%x: (2) 2\n", loc20);
    printf("%s\n", loc20(true) ? "True" : "False");
}