---- MODULE RejectWhileNonfreshExtraction ----
\* Expect: rejected, `DesugarError.whileNotLabelled`. The `while` is preceded by another
\* statement (`print 1`) in the same segment — nothing labels the `while` itself. Real
\* PlusCal's default (non-`-label`) behavior rejects this rather than inventing a label,
\* and this compiler matches that: it does not auto-insert a "loop$N" label here.

(*--algorithm RejectWhileNonfreshExtraction {
    variable x = 3;
    process (P = 0) {
    p1: print 1;
        while (x > 0) {
            x := x - 1;
        };
        print 2;
        goto p1;
    }
}*)

====
