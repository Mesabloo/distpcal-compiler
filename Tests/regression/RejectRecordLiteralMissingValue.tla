---- MODULE RejectRecordLiteralMissingValue ----
\* Expect: rejected at the parser, `E0002`, pointing at the `]` that stands where the second
\* record field's value should be (`8:25`) — not relocated to the operator name or the bracket.
\*
\* `parseAtom`'s `[`-forms are one production that commits after `[ <field> |->`, so the
\* missing-value failure surfaces at the failure point.

Foo == [ a |-> 1, b |-> ]
====
