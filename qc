#!/bin/bash

[[ -z "$1" ]] && echo "expected FILENAME" && exit 1
# [[ "$1" == *".kc" ]] && echo "ONLY filename. this program will add '.kc' to your arg." && exit 1
file=$(basename "$1" .kc)

# we should minimize warnings, if any.
# some are expected, hard to eliminate (which?)
cabal run kc -- "$file.kc" --output-c && cc "test.c" -Wunused -o "$file.out" && ./"$file.out"
