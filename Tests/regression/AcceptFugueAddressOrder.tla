---- MODULE AcceptFugueAddressOrder ----
\* Expect: accepted. `Fugue` exports the order on `Address` -- `\prec`, `\preceq`, `\succ`,
\* `\succeq` -- which the type checker does not otherwise have: `Address` is atomic with equality
\* only, so `a < b` is a type error (`<` is `Int x Int -> Bool`), while the generated Go needs an
\* order on addresses regardless. Reaching code generation is the point -- the four compile to
\* `comm.AddressOrd`'s `Lt`/`Le`/`Gt`/`Ge`.

EXTENDS Fugue

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptFugueAddressOrder {
    process (node \in Nodes)
        variables
            \* @type: Address;
            peer = self;
    {
    p1: await (peer \prec self) \/ (peer \preceq self)
             \/ (self \succ peer) \/ (self \succeq peer);
        peer := self;
        goto Done;
    }
}*)

====
