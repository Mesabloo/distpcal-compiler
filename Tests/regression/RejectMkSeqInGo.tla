---- MODULE RejectMkSeqInGo ----
\* Expect: rejected at the Go backend (E0061). `Fugue!MkSeq(N, Op)` is the total sequence
\* constructor [i \in 1..N |-> Op(i)]. It type-checks -- unlike FunAsSeq/SetAsFun it is safe, so
\* it raises no -Wunsafe -- but its second argument is an operator, and passing an operator as an
\* argument has no Go counterpart without LAMBDA (OPEN_QUESTIONS 9.10), so the backend rejects it.

EXTENDS Fugue

CONSTANTS
    \* @type: Address;
    PID

\* @type: (Int) => Int;
Sq(i) == i * i

(*--algorithm RejectMkSeqInGo {
    process (P = PID)
        variables
            \* @type: Seq(Int);
            s = <<>>;
    {
    p1: s := MkSeq(3, Sq);
        goto Done;
    }
}*)

====
