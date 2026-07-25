---- MODULE RejectUnlabelledStatement ----
\* Expect: rejected, `DesugarError.unlabelledStatement`. A thread's very first statement
\* must be labeled (PlusCal manual §3.7) — `x := 1;` here precedes the thread's first
\* label (`p1`), so there is no label to attach it (or the block it starts) to.

(*--algorithm RejectUnlabelledStatement {
    variable x = 0;
    process (P = 0) {
        x := 1;
    p1: print x;
        goto p1;
    }
}*)

====
