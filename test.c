#include <stdbool.h>
#include <stdio.h>

static int loc5;

static int g4br_br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0 (int (*loc16)(int (int (int, int), int, int)
,int (int, int)
,int
,int), int (*loc17)(int (int, int),int,int), int (*loc18)(int
,int), int loc19, int loc20) {
    return loc16(loc17, loc18, loc19, loc20);
}

static int g3br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0 (int (*loc12)(int (int, int)
,int
,int), int (*loc13)(int,int), int loc14, int loc15) {
    return loc12(loc13, loc14, loc15) + loc5;
}

static int g2br_t0_t0_ret_t0 (int loc10, int loc11) {
    return loc10 + loc11 + loc5;
}

static int g1br_br_t0_t0_ret_t0_t0_t0_ret_t0 (int (*loc7)(int
,int), int loc8, int loc9) {
    return loc7(loc8, loc9);
}

int main ( ) {
    loc5 = 69;
    int loc6 = loc5;
    printf("%d\n", g2br_t0_t0_ret_t0(42, 69));
    printf("%d\n", g4br_br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0(g3br_br_br_t0_t0_ret_t0_t0_t0_ret_t0_br_t0_t0_ret_t0_t0_t0_ret_t0, g1br_br_t0_t0_ret_t0_t0_t0_ret_t0, g2br_t0_t0_ret_t0, 1, 2));
    printf("%d\n", loc5);
}