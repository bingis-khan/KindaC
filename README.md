# KindaC

hehe

The plan is to do the whole pipeline (except codegen) in order to typecheck and import prelude automatically to files.


## current

- typeclass constraints
  - including the funny declaration, where it looks like a type, but it's actually a typeclass.
- associated types

Not sure about ALGO tho. Maybe I'll reannotate code with this. Most of the docs are in separate text files in doc/compiler/ and a small minority in doc/design/.


## directory structure

- `src/` - haskell compiler source
- `kcsrc/` - std
- `test/` - test directory, including test cases
- `doc/` - documentation (README inside)
- `error-handling/` - put files here, when error is stupid or unreadable
- `ctest/` - testing stuff in C
- `incorrect/` - files which do not compile / produce incorrect results

## regressions

- in test 5.08, there are two environments in the union instead of one for a generalized function over typeclass instance. i'll have to check if it also happens for normal functions, what kind of regression it is. happened after removing RemoveUnused, so it's obvious something like this would happen. check if there are any warnings in tests when compiling C programs.


## todo larger

- declaring typeclass constraints, associated types
- module importing and namespaces
- line folding
- error location + actual errors
- integers in types (typed C arrays)  (maybe put this earlier to support C-style arrays)
- finish (actually fix) recursion


## todo

- this is kinda important: for semantics, we need to ensure, that the type of the instance function matches the class function. is there a SMART way to do it (by unification instead of validation?)
  - this is funny. i'm restricting the language. it's already more powerful, but i'm trying to make it less powerful... why would i do that?
    - i think in this case, errors would be pretty bad. like, you will get errors at instantiation when the type becomes known and the class fun types change. very unreadable.
- external functions
  - later try to define a type for a C Function type.
  - and make it illegal to pass normal functions as C function types (make the user go through deconstruction to account for the possible environment)
- make assignments deconstructable.
- in a record deconstruction, if you don't specify the right side (after ':'), bind the member to the variable of the same name.
- when updating records, bind the current variable to the expression. ex: `p = p { v1: v1 { z = 0 } }` <- here, `v1` is bound only on the right side of ':'. No need to write `p.v1` like in Haskell.
- string interpolation! `'Just rammed \(num-glowies) glowies with my car.'` (support only variables inside, seems simpler)
  - think about internationalization? apparently,that's the biggest drawback of string interpolation
- kinds? fixpoint?
- change testing so that:
  - tests are grouped by their type
  - with this, instead of having 4 seperate entries for a single test, make it 1.
- add tests for incorrect compilations
  - right now just check if compilation failed with errors
  - later check error messages
  - (or just check the datatypes!)
  - not sure which is better


### todo misc
- better error *messages*
  Instead of this
  ```
     |
  15 |  false
     |  ^
  unexpected 'f'
  expecting '#' or uppercase letter
  ```
  write something like "expecting constructor (or annotation)". also, when I write the bootstrapped compiler, errors should be better, as I'll write my own parser.
- look for places with recoverable errors
- incorrect indentation if/elif/else when pretty printing AST
- better errors for extraenous symbols (try writing `print x y`)
- scoping - make redefining a datatype an error? or only in the same scope
- [??] super slow on nested functions: `::::::::::::::::1`
  - not currently! but when I change something minor, it happened? so kinda weird. might be a laziness problem.
  - yeah, even with the rewrite, it became slow for some reason. why? it shouldn't be slow now.
  - it might also be a repeated substitution problem? but also laziness maybe??
- mark unused variables and modify the generated code to not generate warnings in C.
- do branching analysis to check if a code path does not return a value.
  - also add a `#[noreturn]` to mark a function that does not return (eg. `exit()`)
- [??] add unit type as default is there are no return statements.
- make another phase "Transform", which transforms case expressions, checks for exhaustiveness of those case expressions, checks for unused code paths and returns.
  - But this will stop me from reporting those errors on functions, which, for example, are already typechecked... So, I'm not sure. I'll have to figure something out.
  - but in general. get rid of `Resolved` and `TyVared`
- Make it so that:
  ```python
    left-only = Left(10)
    print-left(left-only)  # right now this is an error, because the type is Either Int a (with a being an "ambiguous" type)

    # In Haskell, it just works. Make it like Haskell.
  ```

## thoughts???
- should I make a separate datatype for each annotation? or should I parse them later and check if they are correct?

## Design Choices

### `<=` on a variable from the environment

```
f ()
  x = 123

  add1 ()
    x <= x + 1

  add1()
  add1()

# vs

f ()
  x =& 123

  add1 ()
    x <&= x + 1

  add1()
  add1()
```

The alternative is to explicitly take a reference and assign to that reference.

I'm not exactly sure if it should stay allowed. When it's from the environment, it causes *the reference* of the variable to be taken and used. If `<=` appears anywhere in the nested function, then, if the function exits, it might reference invalid memory.

However, it's easier to copy code around without changing stuff. In most cases, user's won't return functions, so it's kinda nice to write like this.

I haven't exactly decided. I want to explicitly pass stuff like the allocator, so "hidden" behavior like this might not fit the "feel" of the language...
