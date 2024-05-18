# KindaC

hehe


# todo
- parse pattern matching
- change VarID, ConID, TypeID to their "typeinfo" datatypes: I think it's more haskell-ish and they are immutable anyway. V
- add types to the ASTPrettyPrinter module so that
  type Context a = a -> Context'
    - I may not end up needing the extra context, as VarInfo, TypeInfo, ConInfo, etc. embed information in them anyway. So no extra context is needed!
- make a separate file for each pretty printing phase + common to avoid duplication
- use relude (better types, nonempty, undefined triggers warning!)
- should I make a separate datatype for each annotation? or should I parse them later and check if they are correct?

# thoughts???
- in resolver, there is a lot of duplication with the new(...), resolve(...) and placeholder(...). Is it okay? Or should I rewrite it?

