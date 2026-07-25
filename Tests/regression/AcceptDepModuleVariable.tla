---- MODULE AcceptDepModuleVariable ----
\* Expect: accepted (standalone -- no embedded algorithm, so well-formedness has nothing to
\* check). Exists purely as an EXTENDS-ed dependency for
\* reject_global_tlaplus_variable_cross_module.tla, to exercise check 2(c)'s cross-module
\* provenance end-to-end: `V` is declared *here*, not in the module that references it.

VARIABLE
    \* @type: Int;
    V

====
