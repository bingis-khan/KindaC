// includes

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef struct{
  
  
  enum {
    MyJust__264t, MyNone__265t
  } tag;
  
  
  union {
    
    
    struct {
      int cMyJust__264__1;
    } MyJust__264;
    #define MyNone__265 ((MyMaybe__261) { .tag = MyNone__265t })
  } uni;
} MyMaybe__261;


static MyMaybe__261 MyJust__264f(int cMyJust__264__1) {
  return (MyMaybe__261) { .tag = MyJust__264t,  .uni.MyJust__264 = { .cMyJust__264__1 = cMyJust__264__1 } };
}

// FUNCTIONS


static MyMaybe__261 is5__262(int x__233) {
  
  if ((x__233 == 5)) {
    return MyJust__264f(x__233);
  }
  
  else {
    return MyNone__265;
  }
}

// MAIN


int main() {
  MyMaybe__261 x__234 = is5__262(12);
  MyMaybe__261 y__235 = is5__262(5);
  MyMaybe__261 z__236 = is5__262(1337);
  MyMaybe__261 temp0 = x__234;
  MyMaybe__261 temp1 = y__235;
  MyMaybe__261 temp2 = x__234;
  MyMaybe__261 temp3 = z__236;
  MyMaybe__261 temp4 = y__235;
  MyMaybe__261 temp5 = z__236;
  printf("%s\n", ((0 ==  memcmp(&temp0, &temp1, sizeof(MyMaybe__261))) == ((0 ==  memcmp(&temp2, &temp3, sizeof(MyMaybe__261))) == (0 ==  memcmp(&temp4, &temp5, sizeof(MyMaybe__261))))) ? "True" : "False");
}

