#include <stdbool.h>
#include <stdio.h>

static int g2br_t0_t0_ret_t0 (int loc6, int loc7) {
    return loc6 + loc7;
}

static int g1br_br_t0_t0_ret_t0_t0_t0_ret_t0 (int loc3 (int
,int), int loc4, int loc5) {
    return loc3(loc4, loc5);
}

int main ( ) {
    printf("%d\n", g2br_t0_t0_ret_t0(42, 69));
    printf("%d\n", g1br_br_t0_t0_ret_t0_t0_t0_ret_t0(g2br_t0_t0_ret_t0, 1, 2));
}