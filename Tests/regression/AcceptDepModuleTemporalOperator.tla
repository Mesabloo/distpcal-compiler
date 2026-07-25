---- MODULE AcceptDepModuleTemporalOperator ----
\* Expect: accepted (standalone -- an ordinary TLA+ operator definition, no embedded algorithm;
\* temporal formulas are only banned *inside* a Distributed PlusCal algorithm, never in the
\* surrounding TLA+ module). Exists purely as an EXTENDS-ed dependency for
\* reject_transitive_temporal.tla, to exercise check 3's transitive half: `IsStable`'s own body
\* contains `[]`, but the algorithm that calls it never writes `[]` itself.

\* @type: (Int) => Bool;
IsStable(x) == [](x = x)

====
