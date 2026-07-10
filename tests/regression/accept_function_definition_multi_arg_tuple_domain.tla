---- MODULE AcceptFunctionDefinitionMultiArgTupleDomain ----
\* Expect: accepted -- a genuinely well-typed 2-binder function definition (`f`'s domain is the
\* 2-tuple `<<Int, Int>>`, matching its 2 binders, per `Elaborator/Declarations.lean`'s `.function`
\* rule) -- but currently REJECTED, a real parser gap rather than a mistake in this fixture.
\* `Parser_/TLAPlus.lean`'s `parseDeclaration` has no production for
\* `CoreTLAPlus.Declaration.function` at all (see `reject_function_definition_domain_not_tuple.
\* tla` for the full explanation) -- every module-level `f[x \in e1, ...] == body` fails to parse
\* today, whether or not its shape would type-check. Once a `parseFunctionDefinition` production
\* is added to `parseDeclaration`, this fixture should start passing without any change to the
\* fixture itself.

EXTENDS Naturals

\* @type: <<Int, Int>> -> Int;
f[x \in {1, 2}, y \in {1, 2}] == x + y
====
