module

public import Parser

@[expose] public section

/--
  A token stream backed by an `Array` with a consumed-count cursor.

  Replaces `Parser.Stream.OfList` as the concrete stream under both parsers. `OfList` stores its
  position as the length of a `past : List` it re-`cons`es on every step, so `getPosition` — called
  on every `withBacktracking`, every choice alternative, twice per `located` — is `O(n)` in the
  number of consumed tokens. `TokenStream` holds the whole token array once and moves an index, so
  `getPosition`/`setPosition` are `O(1)` and `located` is array indexing.
-/
structure TokenStream (τ : Type _) where
  /-- Every token, consumed and remaining. Never changes after construction. -/
  toks : Array τ
  /-- Number of tokens consumed; the current position. Always `≤ toks.size`. -/
  idx : Nat := 0
  deriving Repr, Inhabited

namespace TokenStream
variable {τ : Type _}

/-- A fresh stream over `toks`, positioned at the start. -/
@[inline]
def ofArray (toks : Array τ) : TokenStream τ := { toks }

/-- Whether every token has been consumed. -/
@[inline]
def atEnd (s : TokenStream τ) : Bool := s.toks.size ≤ s.idx

/-- The token at absolute index `n`, or `panic` — for `located`, which only ever asks for indices
inside a span the parser has already crossed. -/
@[inline]
def get! [Inhabited τ] (s : TokenStream τ) (n : Nat) : τ := s.toks[n]!

instance : Parser.Stream (TokenStream τ) τ where
  Position := Nat
  getPosition s := s.idx
  setPosition s p := { s with idx := min p s.toks.size }
  next? s :=
    if h : s.idx < s.toks.size then
      some (s.toks[s.idx], { s with idx := s.idx + 1 })
    else
      none

end TokenStream
