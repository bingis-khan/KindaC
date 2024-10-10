# KindaC

hehe

The plan is to do the whole pipeline (except codegen) in order to typecheck and import prelude automatically to files.

## directory structure

- `src/` - haskell compiler source
- `kcsrc/` - std
- `test/` - test directory, including test cases
- `doc/` - documentation (README inside)
- `error-handling/` - put files here, when error is stupid or unreadable
- `ctest/` - testing stuff in C
- `old/` - old compiler


## todo

### todo BIG ASS BUGS and DESIGN MISTAKES
- make declared tvars (ex. fun (x a, y b), etc.) have a UNIQUE ID, because right now it's possible to confuse the compiler (during environment resolution!! in the Env Union, 'a's from different functions might meet and it would be annoying to distinguish them (it's possible: use function ID + tvar))
- resolving environments in previously declared tvars (before the struct declaration) is broken.
  - !!!! instead of using an ID with Maps, just actually replace them with the objects (they are going to be pointers anyway.) Make 'Eq' and 'Ord' still use the ID. Win-Win!
- resolving environments in previously declared tvars (in ANOTHER module) will be broken.
- !!!! Fix union instantiation (see 1. REQUIRED of doc/compiler-construction/problems)

### todo misc
- parse pattern matching
- [V] change VarID, ConID, TypeID to their "typeinfo" datatypes: I think it's more haskell-ish and they are immutable anyway.
- add types to the ASTPrettyPrinter module so that
  type Context a = a -> Context'
    - I may not end up needing the extra context, as VarInfo, TypeInfo, ConInfo, etc. embed information in them anyway. So no extra context is needed!
     - but context is nice for optional parameters, like, say, you want to pretty print the types or you don't want to print types in expression leaves.
- make a separate file for each pretty printing phase + common to avoid duplication
- use relude (better types, nonempty, undefined triggers warning!)
- better errors *messages*
  Instead of this
  ```
     |
  15 |  false
     |  ^
  unexpected 'f'
  expecting '#' or uppercase letter
  ```

  write something like "expecting constructor (or annotation)"
- look for places with recoverable errors
- incorrect indentation if/elif/else when pretty printing AST
- shitty names for functions newVar and lookupVar in Typecheck.hs
- better errors for extraenous symbols (try writing `print x y`)
- scoping - make redefining a datatype an error? or only in the same scope
- clean Typecheck module (it's gotten bad again, especially the generalization/subSolve part - think about where do FTVs come from, should env ftvs come from data definitions and types? I should put the future `generalize` function near the `subSolve`, because they deal with similar things)
- Environment should be a Set / Set of Sets, but right now it's a list, because we can't put 'Ord' constraints in fmap.
- I had to replace `transverse` with their implementation due to the "forall" type of `transverse`. I wonder if there is a dedicated function instead of `transverse` - I can probably grep through the source by the implementation `cata (fmap embed . n)`.
- `noFunEnv` and the whole imlementation of the algorithm is shaky at best, utterly disgusting at worst. just... fix this. `noFunEnv` is like the worst. incorrect state possible... it's fucked.
- why are parameters being unified???
- super slow on nested functions: `::::::::::::::::1`
- mark unused variables and modify the generated code to not generate warnings in C.
- do branching analysis to check if a code path does not return a value.
  - also add a `#[noreturn]` to mark a function that does not return (eg. `exit()`)
- environments for datatypes (I'll do it after monomorphization/codegen, because I want to know what I'm getting myself into)
- add unit type as default is there are no return statements.
- eliminate the pretty printing module for the AST - since I'm switching to separate ASTs, I can just implement everything as an implementation of Show?
- MEMOIZING AND DIRECT REFERENCES: change Typecheck/Mono ASTs to those, that directly reference functions (Either UniqueVar Function). This will stop requiring us to use Maps for Monomorphization. Make sure to allow memoizing by UniqueVar.
- Maybe the monomorphized AST should be an actual AST (starting from Main, without function list). This would also be pretty easy to compile and it would help with future interpretation..? And maybe it'll be easier to generate output programs?


## thoughts???
- should I make a separate datatype for each annotation? or should I parse them later and check if they are correct?

