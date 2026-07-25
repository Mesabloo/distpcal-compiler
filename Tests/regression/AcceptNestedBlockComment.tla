---- MODULE AcceptNestedBlockComment ----
\* Expect: accepted. `Parser_/TLAPlus.lean`'s block-comment lexer recurses into itself
\* (`blockComment ... (inner := true)`) so `(* ... (* ... *) ... *)` nests properly rather than
\* the outer comment ending at the first `*)` it sees. Placed after a real declaration, not before
\* the module header -- comments before `---- MODULE ... ----` aren't accepted at all currently
\* (a separate, pre-existing parser limitation, `Parser_/TLAPlus.lean`'s `parseModule'` has a
\* `TODO: handle junk before module start`), so this fixture isolates nesting specifically.

EXTENDS Naturals

\* @type: Bool;
x == TRUE

(* outer (* nested *) comment *)
====
