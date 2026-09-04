---- MODULE RejectWeakFairnessNotParsed ----
\* Expect: rejected at the parser, `E0002` at the `WF_` keyword. `WF_x` lexes as the keyword
\* `WF_` followed by the identifier `x` — not one identifier — so the parser meets `WF_` with no
\* rule for fairness formulas and stops there.
\*
\* The fixture pins the split: the error spans exactly `WF_` (11:9-11:12). A change that let
\* `WF_x` lex whole would move the error or drop it (the call would parse as an operator call).

VARIABLE x
Next == x' = x
Spec == WF_x(Next)
====
