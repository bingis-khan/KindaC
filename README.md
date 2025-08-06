# KindaC

hehe

The plan is to do the whole pipeline (except codegen) in order to typecheck and import prelude automatically to files.


## current


--

REALLY BAD PERFORMANCE AND MEMORY USE. WHY?
I GUESS I NEED SOME PROFILING AFTER I'M FINISHED WITH THE GRIND.


I didn't add tests for: line folding, modules, type classes, external functions!

(note: currently, instance generalization and instantiation is scuffed, but in a weird way: it's actually more powerful, so I'm able to write all the classes and instances I want. but it's also super weird. after I implement modules and errors, I want to redo it, so that it matches Rust or similar.... or maybe I'll use this somehow?)

No circular dependency checking

Not sure about ALGO tho. Maybe I'll reannotate code with this. Most of the docs are in separate text files in doc/compiler/ and a small minority in doc/design/.


## directory structure

- `src/` - haskell compiler source
- `kcsrc/` - std
- `test/` - test directory, including test cases
- `doc/` - documentation (README inside)
- `error-handling/` - put files here, when error is stupid or unreadable
- `ctest/` - testing stuff in C
- `incorrect/` - files which do not compile / produce incorrect results
- `future-tests/` - files which I should make tests out of


## regressions

- in test 5.08, there are two environments in the union instead of one for a generalized function over typeclass instance. i'll have to check if it also happens for normal functions, what kind of regression it is. happened after removing RemoveUnused, so it's obvious something like this would happen. check if there are any warnings in tests when compiling C programs.


## todo larger

- integers in types (typed C arrays)  (maybe put this earlier to support C-style arrays)
- finish (actually fix) recursion
- typeclass constraints
  - including the funny declaration, where it looks like a type, but it's actually a typeclass.
    - i have a basic version of this, but the rules are not very finalized... like, force tvars for parameters, but allow nested types for the return type?
  - moved this down, because... it's stupid, but currently we 
- associated types
- extremely bad perf and memory usage (especially when using class functions)
- generating too many types (probably because unions that are equivalent are treated as distinct types)


## todo

- VERY BAD TYPECHECKING, BECAUSE WE ACTUALLY HAVE TO INCLUDE FUNCTION TYPE INFORMATION INTO UNIONS. I GUESS I SHOULD JUST DITCH THE EXTRA UNION PARAMETER AND SILENTLY ADD THEM.
  - although, I might just make a second field in TypeF, which won't be displayed in error messages!
- [V] printing context that does not rely on a global variable / special printing context for errors (it solves the problem of types disappearing when not printing IRs)
- remember, that type associations create new unions and create extra mono functions even though they are instantiated with the same instances. somehow fix that / unify them? (check lingering/)
- better arch for errors and less ugly errors. lots of redundand work, kind of icky algorithms. abstract it more, so I can make better looking errors.
- figure out HOW should the errors look like (including spacing n shi) and then make it look like so.
- add proper end offset without trailing whitespace.
- better errors (eg. type mismatch IN +, in call, should present the whole type)
  ```
   error: type mismatch between Int and Bool
     |
   8 | f(2 == True)
     | ^--- this one has type Int

     |
   8 | f(2 == True)
     | ^^^^^^^^^^^^--- this one has type Bool
  ```
  - it's actually incorrect. the argument types are mismatched, but we display the difference between the two whole structures.
  - we should probably unify arguments separately?
- add circular dependency checking for modules
- lots tests for modules, namespaces and importing.
- this is kinda important: for semantics, we need to ensure, that the type of the instance function matches the class function. is there a SMART way to do it (by unification instead of validation?)
  - this is funny. i'm restricting the language. it's already more powerful, but i'm trying to make it less powerful... why would i do that?
    - i think in this case, errors would be pretty bad. like, you will get errors at instantiation when the type becomes known and the class fun types change. very unreadable.
- external functions
  - later try to define a type for a C Function type.
  - and make it illegal to pass normal functions as C function types (make the user go through deconstruction to account for the possible environment)
- make assignments deconstructable.
- make lambda arguments deconstructable
- in a record deconstruction, if you don't specify the right side (after ':'), bind the member to the variable of the same name.
- when updating records, bind the current variable to the expression. ex: `p = p { v1: v1 { z = 0 } }` <- here, `v1` is bound only on the right side of ':'. No need to write `p.v1` like in Haskell.
- [V] string interpolation! `'Just rammed \(num-glowies) glowies with my car.'` (support only variables inside, seems simpler)
  - [ ] think about internationalization? apparently,that's the biggest drawback of string interpolation
- kinds? fixpoint?
- change testing so that:
  - tests are grouped by their type
  - with this, instead of having 4 seperate entries for a single test, make it 1.
- add tests for incorrect compilations
  - right now just check if compilation failed with errors
  - later check error messages
  - (or just check the datatypes!)
  - not sure which is better
- add more line folding logic where appropriate
- decide if we should replace `while` with `loop` and `break`s.
  - also decide if im adding a for-loop (the one which works on iterables)


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


### `not` should be a function instead of an operator?

Like the title says. Instead of a slightly weird operator, make it a function:

```python
if not x or y
  pass

if not(x) or y
  pass

if not (x or y)
  pass
```

That would be an interesting choice. IMO `not` in Python was always slightly weird syntactically.


### design of `Mem` module

Imagine: `alloc` allocates a SLICE!

```
Slice a
  ptr Ptr a
  count Size  # *currently Int
```

The size of an element should be inferred from `a` (but getting the size is also funny - see later)


### getting sizes of things

Examples of a possible interface:

```
size = Mem.size(x)  
size = size-of(x)  # common word, so maybe a different one would be better if it's going to be imported by default?
size = x size-of() # uglier postix

size = size-of-proxied(Proxy as Proxy SomeBigType)  # this should be a lighter version.
size = size-of-pointed(&x)  # bad fun name geg
size = ptr-size-of(&x)  # shorter, but less descriptive?
size = size-of-elem(slice)  # nice!
```

Currently, we have to pass the whole value to some function to get its size. Inside, we explicitly create an undefined value and then C `sizeof` it. Ideally we should optimize this.


### ffi and interacting with the "base layer" (eg. C, LLVM, my own stuff)

For ffi, I have the `external` keyword. They are a quick addition, so the AST does not fully understand this and I hacked it by adding a special annotation.

I should think about how my language should interact with the base layer. Currently, for ffi, I rely on C's weak type system where I'm using `Int`s everywhere. I should have special C types for FFI n shi.

Another thing are common operations, eg. addition, casting, sizeof-ing, etc. Currently, it's text substitution hacks on top of external functions. How do I represent this? Special AST nodes? Special annotations? I want it to be possible to overload addition, but how do I generate basic operations?

Maybe something like:

```
  # keyword tbd
  baselayer add-f32(l F32, r F32) -> F32

  # or reduce keywords:
  #[baselayer]
  external add-f32(l F32, r F32) -> F32
```

These functions will then have to be implemented by the backend. Nice. But, how do we interact with them in code? They are function declarations, so how would they interact in this context?

Maybe not even define them textually, they will only be a part of the compiler. It'll be a special AST node for these, so they won't be used as functions n shi. Like, special syntax:

```
  %add-f32(1.0, 2.0)
```

But what if we want to do something `proxy-size-of()` which requires a type itself? So its type is not concrete. Then, we would have to define this function in userspace...
I guess, a function like `get-typesize`, which would return a `TypeSize a: TypeSize Int` and then we would have to cast the result type! But still, it's polymorphic, so might be kind of hard. This `TypeSize` may be some generic struct and only in userspace it'll be treated as a thing.

How do other languages do that?

### naming convention: `slice-try-get` vs `Slice.try-get`

Also modularity - more modules or less? Like, it's less annoying to import same modules.

```
  xs slice-get(5)
  xs Slice.get(5)
  Slice.get(xs, 5)

  # not counted
  xs get(5)
```

I think the first one is the least ugly......

I might also do a Getter typeclass, which will unify all the `get()` functions (and also probably will support indexing `[x]` by extension)
