---- MODULE RejectSetCollectMissingOperand ----
\* Expect: rejected at the parser, `E0002`, pointing at the `}` that stands where the `+`
\* operator's right operand should be (`8:25`) — not relocated to the operator name or the brace.
\*
\* `parseAtom`'s `{`-forms are one production that commits after `{ x \in S :`, so the
\* set-collect body's missing operand surfaces at the failure point.

Bar == { x \in S : x +  }
====
