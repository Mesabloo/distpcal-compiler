import Parser
import Extra.List
import Common.Position
import Common.Errors

def Parser.Stream.OfList.map {α β : Type _} (f : α → β) (s : Parser.Stream.OfList α) : Parser.Stream.OfList β where
  next := s.next.map f
  past := s.past.map f

def ParserT.mapStream {τ₁ τ₂ α : Type _} {m : Type _ → Type _} [Monad m]
                              (f : τ₂ → Option τ₁) (g : τ₁ → τ₂) (p : SimpleParserT (Parser.Stream.OfList τ₁) τ₁ m α) : SimpleParserT (Parser.Stream.OfList τ₂) τ₂ m α := λ s ↦
  let n := s.past.length
  let s' : Parser.Stream.OfList τ₁ := { next := s.next.filterWhile f, past := [] }
  -- Offsets in s' are computed from 0 since `past := []` in `s'`
  -- Hence in `mapError` we have to offset all errors by the size of `s.past` (`n` above)
  p.run s' <&> λ | .error s' e => .error {next := s.next.drop s'.past.length, past := s'.past.map g ++ s.past} (mapError n e)
                 | .ok s' r => .ok {next := s.next.drop s'.past.length, past := s'.past.map g ++ s.past} r
where
  mapError : Nat → Parser.Error.Simple (Parser.Stream.OfList τ₁) τ₁ → Parser.Error.Simple (Parser.Stream.OfList τ₂) τ₂
    | n, .unexpected pos tk => .unexpected (pos + n) (g <$> tk)
    | n, .addMessage err pos msg => .addMessage (mapError n err) (pos + n) msg

def Parser.Result.isOk {ε σ α} : Parser.Result ε σ α → Bool
  | .ok .. => true
  | .error .. => false

@[unbox]
structure PositionedSlice where
  slice : String.Slice
  position : Cursor
  deriving Inhabited

open Function in
instance : LT PositionedSlice where
  lt := (· < ·) on PositionedSlice.position

open Function in
instance : LE PositionedSlice where
  le := (· ≤ ·) on PositionedSlice.position

open Function in
instance : BEq PositionedSlice where
  beq := (· == ·) on PositionedSlice.position

instance : DecidableLT PositionedSlice := λ p₁ p₂ ↦ clean% by
  change Decidable (p₁.position < p₂.position)
  infer_instance

instance : DecidableLE PositionedSlice := λ p₁ p₂ ↦ clean% by
  change Decidable (p₁.position ≤ p₂.position)
  infer_instance

instance : Parser.Stream PositionedSlice Char where
  next? s :=
    s.1.front? >>= λ c ↦
      let pos := if c == '\n' then ⟨s.2.line + 1, 0⟩ else {s.2 with col := s.2.col + 1}
      return (c, ⟨s.1.drop 1, pos⟩)
  Position := PositionedSlice
  getPosition s := s
  setPosition _ s := s


instance : Inhabited (Parser.Stream.Position PositionedSlice) := inferInstanceAs (Inhabited PositionedSlice)
instance : BEq (Parser.Stream.Position PositionedSlice) := inferInstanceAs (BEq PositionedSlice)
instance : LT (Parser.Stream.Position PositionedSlice) := inferInstanceAs (LT PositionedSlice)
instance : LE (Parser.Stream.Position PositionedSlice) := inferInstanceAs (LE PositionedSlice)
instance : DecidableLT (Parser.Stream.Position PositionedSlice) := inferInstanceAs (DecidableLT PositionedSlice)
instance : DecidableLE (Parser.Stream.Position PositionedSlice) := inferInstanceAs (DecidableLE PositionedSlice)

instance {σ τ : Type _} [Parser.Stream σ τ] [Repr (Parser.Stream.Position σ)] : Repr (Parser.Stream.Segment σ) :=
  inferInstanceAs (Repr (_ × _))


-- TODO: uniformize `Located` and `Located'`
structure Located (α : Type _) where
  segment : Parser.Stream.Segment PositionedSlice
  data : α
  deriving Functor

instance {α : Type _} [Repr (Parser.Stream.Segment PositionedSlice)] [Repr α] : Repr (Located α) where
  reprPrec l _ :=
    .bracket
      "{ "
        ("segment" ++ " := " ++ .group (.nest 11 <| repr l.segment) ++ .line ++
          "data" ++ " := " ++ .group (.nest 11 <| repr l.data) ++ .line)
      " }"

instance {α} [Inhabited α] : Inhabited (Located α) where
  default := {
    segment := ⟨default, default⟩
    data := default
  }

/-- A piece of data is located if its span in the stream is fully known. -/
@[unbox]
structure Located' (α : Type _) : Type _ where
  segment : SourceSpan
  data : α
  deriving Repr, Inhabited, DecidableEq, BEq --, Hashable


deriving instance Repr for Parser.Stream.OfList
-- deriving instance DecidableEq for String.Slice


structure Unexpected (α : Type _) where
  token : Option α
  pos : SourceSpan
  hints : List String
  deriving Repr, Inhabited

instance {α} [ToString α] : ToString (Unexpected α) where
  toString unexpected := s!"unexpected {if let .some tk := unexpected.token then toString tk else "token"} at {unexpected.pos}"

instance {α} [ToString α] : CompilerDiagnostic (Unexpected α) String where
  isError := true
  msgOf err := toString err
  posOf err := err.pos
  hintsOf err := err.hints


open Parser hiding takeMany1

/--
  `debug p` instruments `p` with some tracing information, outputted with `dbgTrace`.

  Prints information regarding when `p` is applied on the input stream (with the current stream position),
  and whether it succeeded or failed (along with the result/error).
-/
@[never_extract, specialize, macro_inline]
def debug {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [Repr ε] [Repr α] [Repr (Stream.Position σ)] (name : String) (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := λ s ↦ do
  -- dbg_trace "{name}> Applying parser (stream position: {repr (Stream.getPosition s)})"
  let res ← p.run s
  -- match res with
  --   | .ok s r => dbg_trace "{name}> Success: {repr r} (stream position: {repr (Stream.getPosition s)})"
  --   | .error s e => dbg_trace "{name}> Error: {repr e} (stream position: {repr (Stream.getPosition s)})"
  return res

/--
  Tries to execute a parser `p` and returns its result.
  If `p` fails without consuming tokens, returns `none`, otherwise fails.
-/
@[specialize]
def eoption {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [BEq (Stream.Position σ)] (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Option α) := λ s ↦ do
  let savePos := Stream.getPosition s
  return match ← p s with
  | .ok s x => .ok s (.some x)
  | .error s e =>
    if Stream.getPosition s == savePos
    then .ok s .none
    else .error s e

set_option linter.unusedVariables false in
/-- `takeMany1 p` applies `p` at least once, collecting the results. Fails if `p` cannot be applied at least once, or if `p` fails while consuming input. -/
def takeMany1 {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [BEq (Stream.Position σ)] (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := λ s ↦ do
  let mut tmp ← p.run s

  let _ : Inhabited (m (Parser.Result ε σ (Array α))) := ⟨pure (.ok s #[])⟩

  if h : !tmp.isOk then
    let .error s e := tmp
    return .error s e
  let .ok s r := tmp
    | unreachable!

  let mut res := #[r]
  let mut stream := s
  tmp ← p.run stream

  while h : tmp.isOk do
    let .ok s r := tmp
    res := res.push r
    stream := s
    tmp ← p.run stream

  -- `tmp` is not ok anymore
  let .error s e := tmp
    | unreachable!
  if Stream.getPosition s == Stream.getPosition stream then
    -- don't worry, `p` did not consume anything in the last iteration
    return .ok s res
  else
    return .error s e

/-- `takeMany p` tries to repeatedly apply `p` until it does not parse, collecting its results. Fails if `p` fails while consuming input at some point. -/
def takeMany {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [BEq (Stream.Position σ)] (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := λ s ↦ do
  match ← takeMany1 p |>.run s with
  | .error s' e =>
    if Stream.getPosition s' == Stream.getPosition s then
      return .ok s' #[]
    return .error s' e
  | .ok s' r => return .ok s' r

/-- A variant of `sepBy1 sep p` which also returns the collected results of the parser `sep`. -/
def sepAccBy1 {ε σ τ α β : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ] [Parser.Error ε σ τ] (sep : ParserT ε σ τ m α) (p : ParserT ε σ τ m β) : ParserT ε σ τ m (List β × List α) := do
  Parser.foldl (λ (xs, ss) (x, s) => (xs.concat x, ss.concat s)) ([← p], []) do
    let y ← sep
    let x ← p
    pure (x, y)

/--
  Tries to apply a parser from the given list of alternatives, starting from the first.
  Returns the first successful parse result.
  If all parsers in the alternative list fail, fails with the error that happened the furthest in the input stream.
-/
@[specialize]
nonrec def first {σ τ α : Type _} {m : Type _ → Type _}
                          [Monad m] [Parser.Stream σ τ] [lt : LT (Stream.Position σ)] [le : LE (Stream.Position σ)] [DecidableRel lt.lt] [DecidableRel le.le]
                          (ps : List (SimpleParserT σ τ m α)) : SimpleParserT σ τ m α := do
  first ps λ e₁ e₂ => match compareError e₁ e₂ with
    | .gt | .eq => e₁
    | .lt => e₂
where
  compareError : Parser.Error.Simple σ τ → Parser.Error.Simple σ τ → Ordering
    | .unexpected p₁ _, .unexpected p₂ _ => if p₁ ≤ p₂ then .lt else .gt
    | e₁@(.unexpected p₁ _), .addMessage e₂ p₂ _ => if p₂ ≥ p₁ then .lt else compareError e₁ e₂
    | .addMessage e₁ p₁ _, e₂@(.unexpected p₂ _) => if p₁ ≥ p₂ then .gt else compareError e₁ e₂
    | .addMessage e₁ p₁ _, .addMessage e₂ p₂ _ => if p₁ ≥ p₂ then .gt else compareError e₁ e₂
  termination_by e₁ e₂ => (e₁, e₂)
  decreasing_by
    all_goals simp_wf; subst_vars
    · apply Prod.Lex.right
      decreasing_trivial
    · apply Prod.Lex.left
      decreasing_trivial
    · apply Prod.Lex.left
      decreasing_trivial
