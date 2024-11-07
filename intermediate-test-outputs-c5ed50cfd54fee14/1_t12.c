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
    MyJust__227t, MyNone__228t
  } tag;
  
  
  union {
    
    
    struct {
      int cMyJust__227__1;
    } MyJust__227;
    #define MyNone__228 ((MyMaybe__224) { .tag = MyNone__228t })
  } uni;
} MyMaybe__224;


static MyMaybe__224 MyJust__227f(int cMyJust__227__1) {
  return (MyMaybe__224) { .tag = MyJust__227t,  .uni.MyJust__227 = { .cMyJust__227__1 = cMyJust__227__1 } };
}

// FUNCTIONS


static MyMaybe__224 is5__225(int x__196) {
  
  if ((x__196 == 5)) {
    return MyJust__227f(x__196);
  }
  
  else {
    return MyNone__228;
  }
}

// MAIN


int main() {
  MyMaybe__224 x__197 = is5__225(12);
  MyMaybe__224 y__198 = is5__225(5);
  MyMaybe__224 z__199 = is5__225(1337);
  MyMaybe__224 temp0 = x__197;
  MyMaybe__224 temp1 = y__198;
  printf("%s\n", (0 ==  memcmp(&temp0, &temp1, sizeof(MyMaybe__224))) ? "True" : "False");
  MyMaybe__224 temp2 = x__197;
  MyMaybe__224 temp3 = z__199;
  printf("%s\n", (0 ==  memcmp(&temp2, &temp3, sizeof(MyMaybe__224))) ? "True" : "False");
  MyMaybe__224 temp4 = y__198;
  MyMaybe__224 temp5 = z__199;
  printf("%s\n", (0 ==  memcmp(&temp4, &temp5, sizeof(MyMaybe__224))) ? "True" : "False");
}

