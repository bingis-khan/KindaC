// includes

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#pragma clang diagnostic ignored "-Wtautological-compare"
#pragma clang diagnostic ignored "-Wparentheses-equality"
// DATATYPES



typedef 
struct {
  int (*cFun__958__1)(int);
} Fun__956;


static Fun__956 Fun__958f(int (*cFun__958__1)(int)) {
  return (Fun__956) { .cFun__958__1 = cFun__958__1 };
}



typedef enum {
  Unit__963
} Unit__961;



typedef struct{
  
  
  enum {
    SomethingElse__962t, AndElse__964t
  } tag;
  
  
  union {
    
    
    struct {
      int cSomethingElse__962__1;
      Unit__961 cSomethingElse__962__2;
    } SomethingElse__962;
    #define AndElse__964 ((Fun__960) { .tag = AndElse__964t })
  } uni;
} Fun__960;


static Fun__960 SomethingElse__962f(int cSomethingElse__962__1, Unit__961 cSomethingElse__962__2) {
  return (Fun__960) { .tag = SomethingElse__962t,  .uni.SomethingElse__962 = { .cSomethingElse__962__1 = cSomethingElse__962__1, .cSomethingElse__962__2 = cSomethingElse__962__2 } };
}

// FUNCTIONS


static int lambda__959(int x__929) {
  return (x__929 + 1);
}

// MAIN


int main() {
  Fun__956 x__930 = Fun__958f(lambda__959);
  (void) x__930;
  printf("Fun\n");
  Fun__960 y__931 = SomethingElse__962f(123, Unit__963);
  (void) y__931;
  printf("Fun\n");
  Fun__960 z__932 = AndElse__964;
  (void) z__932;
  printf("Fun\n");
}

