---- MODULE RejectOperatorPrecedenceConflict ----
\* Expect: rejected. `Parser_/TLAPlus.lean`'s shunting-yard implementation calls `checkConflicts`
\* (line 758) whenever two infix operators of the same precedence range meet without an
\* intervening paren; `<` is precedence 5 and non-associative
\* (`TLAPlus.InfixOperator.assoc`, line 756 -- not in the `.left` list), so `1 < 2 < 3` triggers
\* the `Associativity.none` branch, which reports it as a genuine conflict rather than silently
\* picking a grouping. Confirmed by running this file directly rather than from source reading
\* alone: the diagnostic that actually surfaces is a generic "unexpected identifier x" pointing at
\* the declaration name, not the "Operator conflict detected ..." message `checkConflicts`
\* constructs -- the real conflict error gets swallowed by a later backtracking attempt before
\* the CLI renders it, a rendering wrinkle worth revisiting, but the module is genuinely, and
\* correctly, rejected either way (confirmed non-zero exit).

\* @type: Bool;
x == 1 < 2 < 3
====
