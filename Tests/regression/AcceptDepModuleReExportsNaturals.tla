---- MODULE AcceptDepModuleReExportsNaturals ----
\* Expect: accepted (standalone -- no embedded algorithm, so well-formedness has nothing to
\* check). Exists purely as an EXTENDS-ed dependency for
\* AcceptTransitiveExtendsThroughUserModule: a *user* module whose own `EXTENDS Naturals` the
\* module extending this one must inherit, and which also declares an operator of its own, so
\* one `EXTENDS` of this module has to deliver both an inherited and an own binding.

EXTENDS Naturals

\* @type: Int;
Threshold == 3

====
