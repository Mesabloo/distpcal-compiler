---- MODULE AcceptSequencesExtendsNaturalsTransitively ----
\* Expect: accepted. `EXTENDS Sequences` alone (no separate `EXTENDS Naturals`) must still bring
\* `Naturals`'s operators into scope, transitively: `Len(y) + 7` needs `Len` (`Sequences`) and
\* `+` (`Naturals`). Matches real TLA+, where `Sequences.tla` itself starts `EXTENDS Naturals`.
\* Regression-covers `Driver/Modules.lean`'s `resolveModule` `.builtin` case resolving a
\* builtin module's own `extends` list the same way it resolves an ordinary file's.

EXTENDS Sequences

\* @type: Seq(Str);
y == <<>>

(* @type: Int; *)
x == Len(y) + 7

====
