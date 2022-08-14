#include <stdbool.h>
#include <stdio.h>



static int g2br_t0_ret_t0 (int);

static int g3br_t0_ret_t0 (int);

static bool g1br_t1_ret_t1 (bool loc6) {
    printf("%d\n", g2br_t0_ret_t0(5));
    return loc6;
}

static int g2br_t0_ret_t0 (int loc7) {
    printf("%d\n", g3br_t0_ret_t0(1));
    return loc7;
}

static int g3br_t0_ret_t0 (int loc8) {
    printf("%s\n", g1br_t1_ret_t1(true) ? "True" : "False");
    printf("%d\n", g2br_t0_ret_t0(1));
    return loc8;
}

int main ( ) {
    int loc13 = 1;
    g3br_t0_ret_t0(1);
    printf("%d\n", 1);
}