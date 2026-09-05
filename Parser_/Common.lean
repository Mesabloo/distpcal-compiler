module

public import Parser
public import Parser_.Stream
import Extra.List
public import Common.Position
public import Common.Errors
meta import CustomPrelude

public section

/--
  A megaparsec-shape parse error, `ε` for every `Parser_` lexer/parser: the token that failed to
  match (`none` at end of input) and every spelling that would have matched there instead.
  `ErrorCombine` unions two same-position errors' `expected`; `Parser_.withErrorMessage` replaces
  one outright, only when its own parser failed without consuming (megaparsec's `<?>`/`label`) —
  never appends, which is what made the old chain-of-messages design repeat `"expected
  expression"` once per level of `parseExpression`'s recursive descent.

  `posOverride`, unset in the ordinary case, is for a sub-parser running over a stream this
  error's own `Stream.Position σ` cannot describe on its own (`Annotations.tryParseAnnotations'`,
  over the flat concatenated comment text): it resolves its own position eagerly, against comment
  boundaries only it has in scope, and hands the result over pre-resolved.
-/
structure ParseError (σ τ : Type _) [Parser.Stream σ τ] where
  pos : Parser.Stream.Position σ
  unexpected : Option τ
  expected : List String := []
  posOverride : Option SourceSpan := none

-- `debug` (below) requires `[Repr ε]` of whatever error type a parser threads, even though its
-- own body never calls `repr` — a documented no-op seam for tracing that isn't wired up yet
-- (`.claude/FINDINGS.md`). Not `deriving`: the `Parser.Stream.Position σ` field is a projection
-- through a typeclass, and the deriving handler cannot infer the `[Repr (Parser.Stream.Position σ)]`
-- hypothesis that needs it.
instance {σ τ} [Parser.Stream σ τ] [Repr (Parser.Stream.Position σ)] [Repr τ] : Repr (ParseError σ τ) where
  reprPrec e _ :=
    .bracket "{ "
      ("pos" ++ " := " ++ .nest 6 (repr e.pos) ++ .line ++
        "unexpected" ++ " := " ++ .nest 13 (repr e.unexpected) ++ .line ++
        "expected" ++ " := " ++ .nest 11 (repr e.expected) ++ .line ++
        "posOverride" ++ " := " ++ .nest 14 (repr e.posOverride) ++ .line)
      " }"

instance {σ τ} [Parser.Stream σ τ] [Inhabited (Parser.Stream.Position σ)] : Inhabited (ParseError σ τ) where
  default := { pos := default, unexpected := none }

instance {σ τ} [Parser.Stream σ τ] : Parser.Error (ParseError σ τ) σ τ where
  unexpected pos tok := { pos, unexpected := tok }
  addMessage e pos msg := { e with pos, expected := [msg] }

/-- How two errors `alt`/`first` found at the *same* position (their job to establish that)
combine into the one actually reported. -/
class ErrorCombine (ε : Type _) where
  combine : ε → ε → ε

instance {σ τ} [Parser.Stream σ τ] : ErrorCombine (ParseError σ τ) where
  combine e₁ e₂ := { e₁ with expected := e₁.expected ++ e₂.expected.filter (!e₁.expected.contains ·) }

-- `Annotations.tryParseAnnotations'` (`Parser_/TLAPlus.lean`) runs over the library's own
-- `Parser.Error.Simple` (`SimpleParser`, deliberately not migrated — its position space is a flat
-- comment string, not any real stream a caller could report against). `alt`/`first` still work
-- over it, just without a real merge: the second alternative's error always wins.
instance {σ τ} [Parser.Stream σ τ] : ErrorCombine (Parser.Error.Simple σ τ) where
  combine _ e₂ := e₂

/-- Render a `ParseError`'s `expected` as the `Unexpected` hint it becomes: nothing when empty;
several spellings become `"expected one of: …"`; one spelling gets `"expected "` prepended if it
reads as a bare noun phrase (`token`'s `toString tk`, `"identifier"`, …, all lowercase-led), or is
shown verbatim if it already reads as a full sentence — either the library's own `char`/`chars`/
`Unicode.*` (`withErrorMessage s!"expected {repr tk}"`, already `"expected "`-led) or fugue's own
direct, capitalized messages (`"Operator conflict …"`, `checkConflicts`) — the one place these
three uses of the same `expected : List String` field are told apart. -/
def ParseError.expectedHints {σ τ} [Parser.Stream σ τ] (e : ParseError σ τ) : List String :=
  match e.expected with
  | [] => []
  | [only] =>
    if only.front.isUpper || "expected ".isPrefixOf only then [only] else [s!"expected {only}"]
  | many => [s!"expected one of: {String.intercalate ", " many}"]

/-- Fail with `tok` unexpected and `items` (bare noun phrases) as the full `expected` set — a
peek-dispatch catch-all's way to name every alternative a `match` itself cannot state, since
`Parser.Error.addMessage` only ever replaces `expected` with one string at a time. -/
def throwExpected {σ τ m α} [Parser.Stream σ τ] [Monad m] (tok : Option τ) (items : List String) :
    ParserT (ParseError σ τ) σ τ m α := λ s ↦
  pure (.error s { pos := Parser.Stream.getPosition s, unexpected := tok, expected := items })

/--
  Run a parser written against one token type inside a parser over another. `f` maps an outer
  token to an inner one (returning `none` at the first token the inner parser has no business
  seeing); `g` maps back. The inner parser sees the maximal `f`-mapped prefix of the tokens not
  yet consumed, indexed from `0`, so `mapError` shifts its reported positions back by the number
  of tokens already consumed. Only the cursor moves in the outer stream — its token array is
  untouched, so the outer tokens `g` would have reconstructed are the originals.
-/
@[nospecialize]
def ParserT.mapStream {τ₁ τ₂ α : Type _} {m : Type _ → Type _} [Monad m]
    (f : τ₂ → Option τ₁) (g : τ₁ → τ₂)
    (p : ParserT (ParseError (TokenStream τ₁) τ₁) (TokenStream τ₁) τ₁ m α) :
    ParserT (ParseError (TokenStream τ₂) τ₂) (TokenStream τ₂) τ₂ m α := λ s ↦
  let n := s.idx
  let inner : Array τ₁ := ((s.toks.toList.drop n).filterWhile f).toArray
  p.run (TokenStream.ofArray inner) <&> λ
    | .error s' e => .error { s with idx := n + s'.idx } (mapError n e)
    | .ok s' r => .ok { s with idx := n + s'.idx } r
where
  mapError (n : Nat) (e : ParseError (TokenStream τ₁) τ₁) : ParseError (TokenStream τ₂) τ₂ :=
    { e with pos := e.pos + n, unexpected := g <$> e.unexpected }

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


-- TODO(located): collapse `Located` and `Located'` into one type.
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

/-- Describes the payload, position dropped — a located value reads the same as its data
wherever only a human-facing description is wanted (`Parser_.token`'s "expected" hints). -/
instance {α} [ToString α] : ToString (Located' α) := ⟨(toString ·.data)⟩

structure Unexpected (α : Type _) where
  token : Option α
  pos : SourceSpan
  hints : List String
  deriving Repr, Inhabited

instance {α} [ToString α] : ToString (Unexpected α) where
  toString unexpected := s!"unexpected {if let .some tk := unexpected.token then toString tk else "token"} at {unexpected.pos}"

instance {α} [ToString α] : CompilerDiagnostic (Unexpected α) String where
  isError := true
  -- One instance covers both the lexer (`α := Char`) and the parser (`α := Token`), so it cannot
  -- tell them apart; `E0002` is the parser's. `DriverError`, which *does* know which ran, reports
  -- `E0001` for the lexer (`Driver/Errors.lean`).
  code _ := Diagnostics.unexpectedToken.code
  msgOf err := toString err
  posOf err := err.pos
  hintsOf err := err.hints

/--
  Warnings raised by the parser itself, as opposed to hard errors (`Unexpected`). Collected
  out-of-band during parsing (`ParserWarningM`, below) rather than emitted immediately, and
  filtered/printed by the compiler driver once parsing returns.
-/
inductive ParserWarning : Type
  /-- `fair process`/`fair+` was parsed and round-tripped, but is never acted on. -/
  | fairIgnored (pos : SourceSpan)
  /-- A comment parses as a well-formed annotation (`@type`/`@mailbox`/`@parameter`) but sits
  where no call site consumes it, so it is silently ignored. Distinct from a *misplaced*
  annotation (captured, but attached to the wrong role), which is a hard error. -/
  | unusedAnnotation (pos : SourceSpan)
  deriving Repr, Inhabited, BEq

/-- The `-W<name>`/`-Wno-<name>` name a given warning is filtered under. -/
def ParserWarning.name : ParserWarning → String
  | .fairIgnored _ => "fair"
  | .unusedAnnotation _ => "unused-annotation"

instance : CompilerDiagnostic ParserWarning String where
  isError := false
  code
    | .fairIgnored _ => Diagnostics.fairIgnored.code
    | .unusedAnnotation _ => Diagnostics.unusedAnnotation.code
  name := ParserWarning.name
  msgOf
    | .fairIgnored _ => "'fair'/'fair+' is parsed but ignored: this compiler does not act on fairness (neither the Go nor the Join Calculus backend's runtime is fairness-aware)."
    | .unusedAnnotation _ => "This annotation has no effect here and will be ignored."
  posOf
    | .fairIgnored pos
    | .unusedAnnotation pos => pos

/-- The base monad every parser in `Parser_` runs against: `Id` plus a `List ParserWarning`
accumulator. -/
abbrev ParserWarningM := StateT (List ParserWarning) Id

/-- The base-monad state a backtrack has to undo, alongside the stream position. For a parser
over `ParserWarningM` that is the accumulated `ParserWarning` list: a warning emitted inside an
alternative that is then abandoned must not survive. `Id` has no such state, so its instance is a
no-op and the lexer pays nothing. -/
class MonadParserBacktrack (m : Type _ → Type _) where
  /-- The part of `m`'s state to snapshot and restore. -/
  Saved : Type
  /-- Take a snapshot. -/
  save : m Saved
  /-- Restore a snapshot. -/
  restore : Saved → m PUnit

instance : MonadParserBacktrack Id where
  Saved := Unit
  save := pure ()
  restore _ := pure ()

instance : MonadParserBacktrack ParserWarningM where
  Saved := List ParserWarning
  save := get
  restore := set


open Parser hiding takeMany1 takeMany eoption first sepBy sepBy1 sepNoEndBy1 sepEndBy1 withBacktracking

/-- `debug name p` runs `p` unchanged. It is the single seam parser tracing is inserted at, and
`name` is the label such a trace would carry; call sites tag themselves once and stay tagged. -/
@[expose, never_extract, specialize, macro_inline]
def debug {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [Repr ε] [Repr α] [Repr (Stream.Position σ)] (_name : String) (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := λ s ↦ do
  let res ← p.run s
  return res

/--
  Tries to execute a parser `p` and returns its result.
  If `p` fails without consuming tokens, returns `none` and rolls back any warnings `p` emitted
  before failing; if `p` fails after consuming input, that failure propagates unchanged.
-/
@[specialize]
def eoption {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Option α) := λ s ↦ do
  let savePos := Stream.getPosition s
  let saved ← MonadParserBacktrack.save
  match ← p s with
  | .ok s x => return .ok s (.some x)
  | .error s e =>
    if Stream.getPosition s == savePos then
      MonadParserBacktrack.restore saved
      return .ok s .none
    else
      return .error s e

set_option linter.unusedVariables false in
/-- `takeMany1 p` applies `p` at least once, collecting the results. Fails if `p` cannot be applied
at least once, or if `p` fails while consuming input. Warnings emitted by the final, failed
(non-consuming) application of `p` are rolled back; warnings from the applications that succeeded
are kept. -/
def takeMany1 {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := λ s ↦ do
  let mut tmp ← p.run s

  let _ : Inhabited (m (Parser.Result ε σ (Array α))) := ⟨pure (.ok s #[])⟩

  if h : !tmp.isOk then
    let .error s e := tmp
    return .error s e
  let .ok s r := tmp
    | unreachable!

  let mut res := #[r]
  let mut stream := s
  let mut saved ← MonadParserBacktrack.save
  tmp ← p.run stream

  while h : tmp.isOk do
    let .ok s r := tmp
    res := res.push r
    stream := s
    saved ← MonadParserBacktrack.save
    tmp ← p.run stream

  -- `tmp` is not ok anymore
  let .error s e := tmp
    | unreachable!
  if Stream.getPosition s == Stream.getPosition stream then
    -- `p` did not consume anything in the last iteration: undo whatever it emitted before failing
    MonadParserBacktrack.restore saved
    return .ok s res
  else
    return .error s e

/-- `takeMany p` tries to repeatedly apply `p` until it does not parse, collecting its results.
Fails if `p` fails while consuming input at some point. Warnings from the final, failed
(non-consuming) application are rolled back. -/
def takeMany {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := λ s ↦ do
  let saved ← MonadParserBacktrack.save
  match ← takeMany1 p |>.run s with
  | .error s' e =>
    if Stream.getPosition s' == Stream.getPosition s then
      MonadParserBacktrack.restore saved
      return .ok s' #[]
    return .error s' e
  | .ok s' r => return .ok s' r

/-! ## Strict (megaparsec) choice combinators

`fgdorais/Parser`'s `OrElse`, `first`, `sepBy*` reset the stream position on *every* failure, so
`p <|> q` is really `try p <|> q` and every `first` alternative is implicitly atomic. These
shadow them with megaparsec semantics: a failure that consumed input propagates, and only a
failure at the entry position falls through to the next alternative. `withBacktracking`
(a.k.a. `try`) is the one sanctioned opt-out, and it now also rolls back base-monad warnings.

Kept in `namespace Parser_` so a parser namespace opts in with `open Parser_` while the lexer,
which still wants the library's backtracking `first`/`<|>` for its symbol trie, simply does not. -/
namespace Parser_

/-- `withBacktracking p` runs `p` and, if `p` fails, rewinds the stream position **and** any
warnings `p` emitted back to the entry point, so a failed `p` leaves no trace. Shadows the
library's, which rewinds the position only. This is megaparsec `try`. -/
@[specialize]
def withBacktracking {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadParserBacktrack m] (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := λ s ↦ do
  let saved ← MonadParserBacktrack.save
  match ← p s with
  | .ok s' v => return .ok s' v
  | .error s' e =>
    MonadParserBacktrack.restore saved
    return .error (Stream.setPosition s' (Stream.getPosition s)) e

/-- `tokenMap test` reads one token and maps it through `test`. **On `none` it fails without
consuming** — the library's `tokenCore` advances the stream *before* the test runs, which turns
every rejected token into a phantom consumption and makes strict `alt`/`first` commit to the
wrong branch. Shadows `Parser.tokenMap`; `tokenFilter`/`token`/`anyToken` sit on top of it. -/
@[specialize]
def tokenMap {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] (test : τ → Option α) : ParserT ε σ τ m α := λ s ↦
  match Stream.next? s with
  | some (tok, s') =>
    match test tok with
    | some x => pure (.ok s' x)
    | none => pure (.error s (Parser.Error.unexpected (Stream.getPosition s) (some tok)))
  | none => pure (.error s (Parser.Error.unexpected (Stream.getPosition s) none))

/-- `tokenFilter test` accepts and returns a token satisfying `test`, failing without consuming
otherwise. -/
@[inline]
def tokenFilter {ε σ τ m} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] (test : τ → Bool) : ParserT ε σ τ m τ :=
  tokenMap λ c ↦ if test c then some c else none

/-- `token tk` accepts and returns `tk`, failing without consuming otherwise. -/
@[inline]
def token {ε σ τ m} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [DecidableEq τ] (tk : τ) : ParserT ε σ τ m τ :=
  tokenFilter (· == tk)

/-- `anyToken` consumes and returns one token, failing (without consuming) only at end of input. -/
@[inline]
def anyToken {ε σ τ m} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] : ParserT ε σ τ m τ :=
  tokenMap some

/-- `alt p q`: run `p`; if it fails **without consuming input**, roll its warnings back and run
`q`; if `p` consumed input before failing, that failure propagates and `q` is never tried. This
is megaparsec `<|>` — wrap `p` in `withBacktracking` to get the retry-after-consumption the
library's `<|>` always gives. When `q` *also* fails at that same entry position, the two errors
combine (`ErrorCombine`) rather than `p`'s being silently dropped — `p <||> q` failing means
"neither matched", and the report should say what either would have accepted. -/
@[specialize]
def alt {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadParserBacktrack m] [BEq (Stream.Position σ)] [ErrorCombine ε] (p q : ParserT ε σ τ m α) : ParserT ε σ τ m α := λ s ↦ do
  let saved ← MonadParserBacktrack.save
  match ← p s with
  | .ok s' v => return .ok s' v
  | .error s' e₁ =>
    if Stream.getPosition s' == Stream.getPosition s then
      MonadParserBacktrack.restore saved
      match ← q s with
      | .ok s'' v => return .ok s'' v
      | .error s'' e₂ =>
        if Stream.getPosition s'' == Stream.getPosition s then
          return .error s'' (ErrorCombine.combine e₁ e₂)
        else
          return .error s'' e₂
    else
      return .error s' e₁

@[inherit_doc alt] infixl:20 " <||> " => alt

/-- `first ps` tries the alternatives in order with megaparsec semantics (see `alt`): the first
that consumes input commits, and only same-position failures fall through. On total failure every
alternative's `expected` is merged into the one reported error. -/
@[specialize]
def first {ε σ τ α : Type _} {m : Type _ → Type _}
    [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [MonadParserBacktrack m] [BEq (Stream.Position σ)] [ErrorCombine ε]
    (ps : List (ParserT ε σ τ m α)) : ParserT ε σ τ m α :=
  match ps with
  | [] => λ s ↦ pure (.error s (Parser.Error.unexpected (Stream.getPosition s) none))
  | [p] => p
  | p :: ps => alt p (first ps)

/-- `withErrorMessage msg p`: if `p` fails without consuming input, replace whatever it expected
with `msg` (megaparsec's `<?>`/`label`); a failure that consumed input propagates untouched.
Shadows the library's `withErrorMessage`, which wraps *unconditionally*: used directly on a
recursive-descent parser like `parseExpression`, every nested call would re-wrap whatever the
previous level had already wrapped, repeating `"expected expression"` once per level. -/
@[specialize]
def withErrorMessage {ε σ τ m α} [Parser.Stream σ τ] [Parser.Error ε σ τ] [Monad m] [BEq (Stream.Position σ)] (msg : String) (p : ParserT ε σ τ m α) : ParserT ε σ τ m α := λ s ↦ do
  match ← p s with
  | .ok s' v => return .ok s' v
  | .error s' e =>
    if Stream.getPosition s' == Stream.getPosition s then
      return .error s' (Parser.Error.addMessage e (Stream.getPosition s') msg)
    else
      return .error s' e

/-- A variant of `sepBy1 sep p` which also returns the collected results of the parser `sep`. -/
@[specialize]
def sepAccBy1 {ε σ τ α β : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ] [Parser.Error ε σ τ] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (sep : ParserT ε σ τ m α) (p : ParserT ε σ τ m β) : ParserT ε σ τ m (List β × List α) := do
  let x ← p
  let rest ← takeMany (do let s ← withBacktracking sep; let y ← p; pure (s, y))
  return (x :: (rest.toList.map (·.2)), rest.toList.map (·.1))

/-- `sepBy1 sep p` parses one or more `p` separated by `sep`, megaparsec-style: `sep` is a probe
(a `sep` that consumes then fails — e.g. its whitespace/comment skip runs before the token check
misses — ends the list cleanly), but once `sep` is in, a `p` that fails after consuming
propagates its error rather than being silently dropped. No trailing `sep` is consumed. -/
@[specialize]
def sepBy1 {ε σ τ α β : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ] [Parser.Error ε σ τ] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  let x ← p
  let xs ← takeMany (withBacktracking sep *> p)
  return #[x] ++ xs

/-- `sepBy sep p` parses zero or more `p` separated by `sep`. Same strictness as `sepBy1` once
the first `p` is in. -/
@[specialize]
def sepBy {ε σ τ α β : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ] [Parser.Error ε σ τ] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  match ← eoption p with
  | some x => (#[x] ++ ·) <$> takeMany (withBacktracking sep *> p)
  | none => return #[]

/-- Alias: under strict semantics `sepBy1` already refuses a trailing `sep`. -/
@[specialize]
def sepNoEndBy1 {ε σ τ α β : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ] [Parser.Error ε σ τ] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) :=
  sepBy1 sep p

/-- `sepEndBy1 sep p` parses one or more `p` separated by `sep` with an **optional trailing
`sep`** — the case where `sep` doubles as a terminator (PlusCal's statement `;`). A `sep` with a
non-`p` after it ends the list; a `p` that fails *after consuming* still propagates its error. -/
partial def sepEndBy1 {ε σ τ α β : Type _} {m : Type _ → Type _} [Monad m] [Parser.Stream σ τ] [Parser.Error ε σ τ] [MonadParserBacktrack m] [BEq (Stream.Position σ)] (sep : ParserT ε σ τ m β) (p : ParserT ε σ τ m α) : ParserT ε σ τ m (Array α) := do
  let x ← p
  loop #[x]
where
  loop (acc : Array α) : ParserT ε σ τ m (Array α) := do
    match ← eoption (withBacktracking sep) with
    | none => return acc
    | some _ =>
      match ← eoption p with
      | none => return acc
      | some y => loop (acc.push y)

end Parser_

end
