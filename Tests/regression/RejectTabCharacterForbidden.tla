---- MODULE RejectTabCharacterForbidden ----
\* Expect: rejected. `Parser_/TLAPlus.lean`'s `ws` lexer explicitly forbids a literal horizontal
\* tab (U+0009) anywhere whitespace is expected, with a dedicated message ("Horizontal tab
\* characters (U+0009) are forbidden."), independent of and more specific than a generic
\* unexpected-character parse error. The tab below sits between `EXTENDS` and `Naturals` (a real
\* `\t` byte, not the two-character escape).

EXTENDS	Naturals
====
