#include <stdbool.h>
#include <stdio.h>

enum t7__ {t7_____14_tag,t7_____15_tag,t7_____16_tag};
struct t8__int_int_t7__ { 
    enum {t8__int_int_t7_____17_tag
    ,t8__int_int_t7_____18_tag
    ,t8__int_int_t7_____19_tag
    ,t8__int_int_t7_____20_tag} t8__int_int_t7____tags;
    union { 
        struct { 
            enum t7__ t8__int_int_t7_____18__0;
             } t8__int_int_t7_____18;
        struct { 
            int t8__int_int_t7_____19__0;
            enum t7__ t8__int_int_t7_____19__1;
             } t8__int_int_t7_____19;
        struct { 
            int t8__int_int_t7_____20__0;
            int t8__int_int_t7_____20__1;
            enum t7__ t8__int_int_t7_____20__2;
             } t8__int_int_t7_____20;
         } t8__int_int_t7____union;
     };
static struct t8__int_int_t7__ t8__int_int_t7_____17_con = {.t8__int_int_t7____tags = t8__int_int_t7_____17_tag} ;
static struct t8__int_int_t7__ t8__int_int_t7_____18_con (enum t7__ t8__int_int_t7_____18__0_param) {
    return (struct t8__int_int_t7__) {.t8__int_int_t7____tags = t8__int_int_t7_____18_tag
    ,.t8__int_int_t7____union.t8__int_int_t7_____18 = {.t8__int_int_t7_____18__0 = t8__int_int_t7_____18__0_param}};
}
static struct t8__int_int_t7__ t8__int_int_t7_____19_con (int t8__int_int_t7_____19__0_param
,enum t7__ t8__int_int_t7_____19__1_param) {
    return (struct t8__int_int_t7__) {.t8__int_int_t7____tags = t8__int_int_t7_____19_tag
    ,.t8__int_int_t7____union.t8__int_int_t7_____19 = {.t8__int_int_t7_____19__0 = t8__int_int_t7_____19__0_param
    ,.t8__int_int_t7_____19__1 = t8__int_int_t7_____19__1_param}};
}
static struct t8__int_int_t7__ t8__int_int_t7_____20_con (int t8__int_int_t7_____20__0_param
,int t8__int_int_t7_____20__1_param
,enum t7__ t8__int_int_t7_____20__2_param) {
    return (struct t8__int_int_t7__) {.t8__int_int_t7____tags = t8__int_int_t7_____20_tag
    ,.t8__int_int_t7____union.t8__int_int_t7_____20 = {.t8__int_int_t7_____20__0 = t8__int_int_t7_____20__0_param
    ,.t8__int_int_t7_____20__1 = t8__int_int_t7_____20__1_param
    ,.t8__int_int_t7_____20__2 = t8__int_int_t7_____20__2_param}};
}
struct t6__t7__ { 
    enum {t6__t7_____12_tag,t6__t7_____13_tag} t6__t7____tags;
    union { 
        struct { 
            enum t7__ t6__t7_____12__0;
             } t6__t7_____12;
         } t6__t7____union;
     };
static struct t6__t7__ t6__t7_____12_con (enum t7__ t6__t7_____12__0_param) {
    return (struct t6__t7__) {.t6__t7____tags = t6__t7_____12_tag
    ,.t6__t7____union.t6__t7_____12 = {.t6__t7_____12__0 = t6__t7_____12__0_param}};
}
static struct t6__t7__ t6__t7_____13_con = {.t6__t7____tags = t6__t7_____13_tag} ;



static struct t8__int_int_t7__ g9br_t8_t8_ret_t8 (struct t8__int_int_t7__ loc32, struct t8__int_int_t7__ loc33) {
    return loc32;
}

static struct t6__t7__ g9br_t6_t6_ret_t6 (struct t6__t7__ loc32, struct t6__t7__ loc33) {
    return loc32;
}

static int g9br_t1_t1_ret_t1 (int loc32, int loc33) {
    return loc32;
}

int main ( ) {
    g9br_t1_t1_ret_t1(1, 2);
    g9br_t6_t6_ret_t6(t6__t7_____13_con, t6__t7_____12_con(t7_____16_tag));
    bool loc34 = true;
    g9br_t8_t8_ret_t8(t8__int_int_t7_____19_con(1, t7_____16_tag), t8__int_int_t7_____20_con(1, 2, t7_____15_tag));
}