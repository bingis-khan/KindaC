#include <stdbool.h>
#include <stdio.h>



static int g2br_t0_ret_t0 (int);

static bool g1br_t1_ret_t1 (bool loc3) {
    int loc4 = g2br_t0_ret_t0(10);
    printf("%d\n", loc4);
    return loc3;
}

static int g2br_t0_ret_t0 (int loc5) {
    printf("%s\n", g1br_t1_ret_t1(true) ? "True" : "False");
    return loc5;
}

static int g1br_t0_ret_t0 (int loc3) {
    int loc4 = g2br_t0_ret_t0(10);
    printf("%d\n", loc4);
    return loc3;
}

int main ( ) {
    printf("%d\n", g2br_t0_ret_t0(1));
    printf("%d\n", g1br_t0_ret_t0(1));
}