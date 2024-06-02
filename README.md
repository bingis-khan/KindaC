# KindaC

hehe

The plan is to do the whole pipeline (except codegen) in order to typecheck and import prelude automatically to files.



# todo
- parse pattern matching
- change VarID, ConID, TypeID to their "typeinfo" datatypes: I think it's more haskell-ish and they are immutable anyway. V
- add types to the ASTPrettyPrinter module so that
  type Context a = a -> Context'
    - I may not end up needing the extra context, as VarInfo, TypeInfo, ConInfo, etc. embed information in them anyway. So no extra context is needed!
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

# thoughts???
- should I make a separate datatype for each annotation? or should I parse them later and check if they are correct?

