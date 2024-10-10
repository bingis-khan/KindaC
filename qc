#!/bin/sh

[[ -z "$1" ]] && echo "expected FILENAME" && exit 1
[[ "$1" == *".kc" ]] && echo "ONLY filename. this program will add '.kc' to your arg." && exit 1

# we should minimize warnings, if any.
# some are expected, hard to eliminate (which?)
stack run -- "$1.kc" --output-c && cc "$1.c" -Wunused -o "$1.out" && ./"$1.out"
