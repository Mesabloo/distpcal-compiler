# Quick description of the various syntax trees

The syntax trees are described in order of appearance in the compiler pipeline.

## TLA+ expressions

* `SurfaceTLAPlus`: the concrete syntax tree output by the parser, with some comments
  kept in some places (for annotation processing).
* `CoreTLAPlus`: a desugared version of `SurfaceTLAPlus`, where `@` is replaced by the
  proper function access, conjunction and disjunction lists are transformed into chains 
  of `/\` and `\/`, etc.
* `TypedTLAPlus`: elaborated version of `CoreTLAPlus` with types attached in some places
  (where relevant).
* `TypedSetTheory`: `TypedTLAPlus`, without all the temporal operators. 

## PlusCal

* `SurfacePlusCal`: the concrete syntax tree output by the parser.
* `CorePlusCal`: desugared version of `SurfacePlusCal`, with all `goto` statements
  explicit, always appearing only at the end of blocks.
* `TypedPlusCal`: elaborated version of `CorePlusCal`, with types attached in some places.
* `GuardedPlusCal`: a restriction of `TypedPlusCal` where all `await`s, `receive`s and
  `with`s are placed at the very beginning of each atomic block.
* `NetworkPlusCal`: a further restriction of `GuardedPlusCal` with no `receive` guards,
  replaced by internal opaque threads.