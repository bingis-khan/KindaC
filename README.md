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

### todo BIG ASS BUGS

- REGRESSION: env expansion is broken. sometimes, tvars declared inside a function appear in the environment when some other polymorphic function is instantiated to these tvars outside. seems to be the whole problem. have to find some other way to know which tvars were declared inside and which ones were not.
- clash with RemoveUnused. it uses only EnvIDs (and ignores types), which is incorrect? however, how did it work? I didn't document it enough...


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
- [??] super slow on nested functions: `::::::::::::::::1`
  - not currently! but when I change something minor, it happened? so kinda weird. might be a laziness problem.
  - yeah, even with the rewrite, it became slow for some reason. why? it shouldn't be slow now.
- mark unused variables and modify the generated code to not generate warnings in C.
- do branching analysis to check if a code path does not return a value.
  - also add a `#[noreturn]` to mark a function that does not return (eg. `exit()`)
- environments for datatypes (I'll do it after monomorphization/codegen, because I want to know what I'm getting myself into)
- [??] add unit type as default is there are no return statements.
- [V] eliminate the pretty printing module for the AST - since I'm switching to separate ASTs, I can just implement everything as an implementation of Show?
- MEMOIZING AND DIRECT REFERENCES: change Typecheck/Mono ASTs to those, that directly reference functions (Either UniqueVar Function). This will stop requiring us to use Maps for Monomorphization. Make sure to allow memoizing by UniqueVar.
- Maybe the monomorphized AST should be an actual AST (starting from Main, without function list). This would also be pretty easy to compile and it would help with future interpretation..? And maybe it'll be easier to generate output programs?
- Maybe represent function arrow (->) as a (predefined) constructor? This might simplify typechecking, because the environments would need to be handled by TCons, which we, as it turns out, already need to do.
- make another phase "Transform", which transforms case expressions, checks for exhaustiveness of those case expressions, checks for unused code paths and returns.
  - But this will stop me from reporting those errors on functions, which, for example, are already typechecked... So, I'm not sure. I'll have to figure something out.
  - but in general. get rid of `Resolved` and `TyVared`
- Make it so that:
  ```python
    left-only = Left(10)
    print-left(left-only)  # right now this is an error, because the type is Either Int a (with a being an "ambiguous" type)

    # In Haskell, it just works. Make it like Haskell.
  ```
- Further simplify unification (make it Monoidal? find some algorithm, which enables me to make Subst composable)


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
