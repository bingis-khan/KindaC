#include <stdbool.h>
#include <stdio.h>

int main ( ) {
    int loc1 = 3;
    int loc2 = loc1 + 6;
    printf("%d\n", loc2);
    printf("%d\n", loc1 + 3);
    if (loc1 == loc2) {
        printf("%d\n", loc1 + loc2 + 69);
        printf("%d\n", loc1);
    }  ;
    if (false) {        
        printf("%s\n", true ? "True" : "False");
    } else if (false) {
        printf("%d\n", 1);
    }
    else if (true) {
        printf("%d\n", 420);
    } else {
        printf("%d\n", 1 + 2 + 3 + 4 + 5 / 10);
    };
}