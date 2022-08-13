#include <stdbool.h>
#include <stdio.h>

static int loc5;

static int g4br_br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0 (int loc15 (int (int (int, int), int, int)
,int (int, int)
,int
,int), int loc16 (int (int, int),int,int), int loc17 (int
,int), int loc18, int loc19) {
    return loc15(loc16, loc17, loc18, loc19);
}

static int g3br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0 (int loc11 (int (int, int)
,int
,int), int loc12 (int,int), int loc13, int loc14) {
    return loc11(loc12, loc13, loc14);
}

static int g2br_t0_t0_ret_t0 (int loc9, int loc10) {
    return loc9 + loc10 + loc5;
}

static int g1br_br_t0_t0_ret_t0_t0_t0_ret_t0 (int loc6 (int
,int), int loc7, int loc8) {
    return loc6(loc7, loc8);
}

int main ( ) {
    loc5 = 69;
    printf("%d\n", g2br_t0_t0_ret_t0(42, 69));
    printf("%d\n", g4br_br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0(g3br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0, g1br_br_t0_t0_ret_t0_t0_t0_ret_t0, g2br_t0_t0_ret_t0, 1, 2));
    printf("%d\n", loc5);
}