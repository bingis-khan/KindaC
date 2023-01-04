#include <stdbool.h>
#include <stdio.h>

struct t6__bool_int { 
    enum {t6__bool_int___14_tag,t6__bool_int___15_tag} t6__bool_int__tags;
    union { 
        struct { 
            int t6__bool_int___14__0;
             } t6__bool_int___14;
        struct { 
            bool t6__bool_int___15__0;
             } t6__bool_int___15;
         } t6__bool_int__union;
     };
static struct t6__bool_int t6__bool_int___14_con (int t6__bool_int___14__0_param) {
    return (struct t6__bool_int) {.t6__bool_int__tags = t6__bool_int___14_tag
    ,.t6__bool_int__union.t6__bool_int___14 = {.t6__bool_int___14__0 = t6__bool_int___14__0_param}};
}
static struct t6__bool_int t6__bool_int___15_con (bool t6__bool_int___15__0_param) {
    return (struct t6__bool_int) {.t6__bool_int__tags = t6__bool_int___15_tag
    ,.t6__bool_int__union.t6__bool_int___15 = {.t6__bool_int___15__0 = t6__bool_int___15__0_param}};
}
enum t5__ {t5_____12_tag,t5_____13_tag};
struct t7__int_t5__ { 
    int t7__int_t5_____16__0;
    enum t5__ t7__int_t5_____16__1;
     };
static struct t7__int_t5__ t7__int_t5_____16_con (int t7__int_t5_____16__0_param
,enum t5__ t7__int_t5_____16__1_param) {
    return (struct t7__int_t5__) {.t7__int_t5_____16__0 = t7__int_t5_____16__0_param
    ,.t7__int_t5_____16__1 = t7__int_t5_____16__1_param};
}



static int g11br_t1_t1_ret_t1 (int loc33, int loc34) {
    return loc33+loc34;
}

static struct t7__int_t5__ g10br_br_t1_t5_ret_t7_t1_t5_ret_t7 (struct t7__int_t5__ (*loc29)(int
,enum t5__), int loc30, enum t5__ loc31) {
    return loc29(loc30, loc31);
}

static int g10br_br_t1_t1_ret_t1_t1_t1_ret_t1 (int (*loc29)(int
,int), int loc30, int loc31) {
    return loc29(loc30, loc31);
}

int main ( ) {
    struct t6__bool_int loc25 = t6__bool_int___14_con(10);
    struct t6__bool_int loc26 = t6__bool_int___15_con(true);
    bool loc27 = true;
    struct t7__int_t5__ loc28 = t7__int_t5_____16_con(1, t5_____12_tag);
    struct t7__int_t5__ loc32 = g10br_br_t1_t5_ret_t7_t1_t5_ret_t7(t7__int_t5_____16_con, 420, t5_____13_tag);
    int loc35 = g10br_br_t1_t1_ret_t1_t1_t1_ret_t1(g11br_t1_t1_ret_t1, 2, 1);
    //bool loc36 = loc25==loc26;
}
