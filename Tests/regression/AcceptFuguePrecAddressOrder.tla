---- MODULE AcceptFuguePrecAddressOrder ----
\* Expect: accepted. `Fugue`'s `\prec`, the order on `Address` the type checker does not otherwise
\* have: `Address` is atomic with equality only, so `a < b` is a type error (`<` is
\* `Int x Int -> Bool`), while the generated Go needs an order on addresses regardless. Reaching
\* code generation is the point of the fixture -- `\prec` compiles to `comm.AddressOrd.Lt`.

EXTENDS Fugue

CONSTANTS
    \* @type: Set(Address);
    Nodes

(*--algorithm AcceptFuguePrecAddressOrder {
    process (node \in Nodes)
        variables
            \* @type: Address;
            peer = self;
    {
    p1: await peer \prec self;
        peer := self;
        goto Done;
    }
}*)

====
