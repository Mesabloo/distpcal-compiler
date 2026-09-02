---- MODULE AcceptFunAsSeqWarns ----
\* Expect: accepted, all the way to Go, and the emitted Go must compile. `FunAsSeq(f)` reads a
\* function back as the sequence it encodes -- undefined unless `DOMAIN f = 1..n`, so the
\* generated program aborts there rather than inventing a value. Every use raises W0008
\* (`-Wunsafe`); `-Wno-unsafe` silences it.
\*
\* `EXTENDS Fugue` alone brings in `Naturals` (the `1..3` range), since a downcast is unusable
\* without it; `Sequences` is still explicit here for `Len`.

EXTENDS Fugue, Sequences

CONSTANTS
    \* @type: Address;
    PID

(*--algorithm AcceptFunAsSeqWarns {
    process (P = PID)
        variables
            \* @type: Int -> Int;
            f = [i \in 1..3 |-> i * i],
            \* @type: Seq(Int);
            s = <<>>;
    {
    p1: s := FunAsSeq(f);
        assert Len(s) = 3;
        goto Done;
    }
}*)

====
