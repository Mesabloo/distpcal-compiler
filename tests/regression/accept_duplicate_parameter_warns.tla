---- MODULE AcceptDuplicateParameterWarns ----
\* Expect: accepted (with a `duplicate-parameter` warning, suppressible via
\* `-Wno-duplicate-parameter`). `@parameter` is a content-free marker, so a repeated one on
\* the same variable doesn't create any real ambiguity (unlike a repeated `@type`/`@mailbox`,
\* which are hard errors) -- it's just redundant.

(*--algorithm AcceptDuplicateParameterWarns {
    process (P = 0)
        variable
            \* @parameter
            \* @parameter
            x \in {"a", "b"};
    {
    p1: skip;
    }
}*)

====
