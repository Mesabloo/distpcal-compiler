---- MODULE SkipFunctionDefinitionDomainNotTuple ----
\* Expect: rejected, `TCError.notATupleType` (`Elaborator/Declarations.lean`'s `.function` case,
\* the `_, got => throw (.notATupleType ...)` branch: 2 binders need the annotation's domain to be
\* a 2-element `Typ.tuple`, not a bare `Int`) -- but currently rejected for a different reason, a
\* real parser gap. `Parser_/TLAPlus.lean`'s `parseDeclaration` (the `first [...]` list right
\* before this module's declaration loop) only ever produces `.assume`/`.constants`/`.variables`/
\* `.operator` -- there is no parser production anywhere that builds a `CoreTLAPlus.Declaration.
\* function` (`f[x \in e1, ..., xn \in en] == body`) at all, even though
\* `Elaborator/Declarations.lean`'s `checkDeclaration` fully implements the `.function` typing
\* rule, `Core/CoreTLAPlus/Syntax.lean` has the constructor, and `Core/SurfaceTLAPlus/Pretty.lean`
\* can print one. So a *module-level function definition* is currently unwritable in concrete
\* syntax, full stop, regardless of whether its shape would ultimately be accepted or rejected;
\* confirmed by testing a plainly well-typed single-binder function definition too (see
\* `accept_function_definition_multi_arg_tuple_domain.tla`), which fails identically. This fixture
\* exits non-zero today for that reason (a parse error, `"unexpected identifier f"`), which happens
\* to match what `reject_*` expects, but only coincidentally -- the intended `notATupleType` check
\* is never actually reached.

EXTENDS Naturals

\* @type: Int -> Int;
f[x \in {1, 2}, y \in {1, 2}] == x + y
====
