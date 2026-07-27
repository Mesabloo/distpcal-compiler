module

meta import CustomPrelude

public section

/-!
  The pipeline's stages, as data.

  Lives under `Common/` rather than next to the pipeline that runs them (`Driver/Pipeline.lean`)
  because two things below the driver need to name a stage without depending on it: the
  diagnostic registry (`Common/Diagnostics/Registry.lean`), which records which stage each code
  comes from, and anything reporting where a compile stopped.
-/

/-- Where a compile is, or where it stopped. Constructor order is pipeline order — `Stage.reaches`
compares two stages by it. -/
inductive Stage : Type
  /-- Source text read; nothing compiled yet. -/
  | read
  /-- Lexing (`Parser_/Tokens`). -/
  | lex
  /-- Parsing (`Parser_/TLAPlus.lean`). -/
  | parse
  /-- `@type`/`@mailbox`/`@parameter` annotation resolution. -/
  | annotation
  /-- Surface → Core desugaring. -/
  | desugar
  /-- `EXTENDS` resolution: locating, and recursively compiling, each dependency. -/
  | resolve
  /-- Type checking (`Elaborator`). -/
  | typeCheck
  /-- The well-formedness restrictions (`WellFormedness`). -/
  | wellFormedness
  /-- `Typed2Computable`. -/
  | computable
  /-- `Computable2Guarded`. -/
  | guarded
  /-- `Guarded2Network`. -/
  | network
  /-- `Network2Go`, the Go backend. -/
  | go
  deriving DecidableEq, Repr, Inhabited, Ord, BEq

namespace Stage

/-- The `-d dump-<name>`/expectation-file spelling of a stage. -/
def name : Stage → String
  | .read => "read" | .lex => "lex" | .parse => "parse" | .annotation => "annotation"
  | .desugar => "desugar" | .resolve => "resolve" | .typeCheck => "typecheck"
  | .wellFormedness => "wellformedness" | .computable => "computable" | .guarded => "guarded"
  | .network => "network" | .go => "go"

instance : ToString Stage := ⟨Stage.name⟩

/-- What `-d dump-<name>` writes out for this stage, and `none` for a stage with nothing worth
writing. Four have nothing: `read` has only the source text the user already has, `resolve`
produces its dependencies' modules rather than one of its own (each dumps itself as it is
compiled), and `annotation`/`wellFormedness` transform nothing — they check, and hand their input
onward unchanged.

One function rather than a `Bool` and a separate description because the two answers must agree:
`fugue help -d` lists exactly the stages with an artifact, labelled with what that artifact is.
Matched exhaustively on purpose: a stage added later must say what it dumps, rather than
defaulting to dumpable and acquiring a `-d` flag that writes nothing. -/
def artifact? : Stage → Option String
  | .read | .annotation | .resolve | .wellFormedness => none
  | .lex => some "the token stream"
  | .parse => some "the surface AST, annotations still attached"
  | .desugar => some "the Core AST, annotations resolved into fields"
  | .typeCheck => some "the typed AST"
  | .computable => some "the computable fragment"
  | .guarded => some "Guarded PlusCal"
  | .network => some "Network PlusCal"
  | .go => some "the emitted Go"

/-- Does this stage produce an artifact worth writing out? -/
def dumpable (s : Stage) : Bool := s.artifact?.isSome

/-- The `-d dump-<name>` option that dumps this stage's artifact. Spelled from `name`, so the flag,
the file it writes (`<dump-dir>/<module>-<name>`) and the stage a diagnostic reports all use one
spelling. -/
def dumpOption (s : Stage) : String := s!"dump-{s.name}"

/-- Every stage, in pipeline order. -/
def list : List Stage :=
  [.read, .lex, .parse, .annotation, .desugar, .resolve, .typeCheck, .wellFormedness,
   .computable, .guarded, .network, .go]

/-- The stage `s` names, if it names one. -/
def ofName? (s : String) : Option Stage := Stage.list.find? (·.name == s)

/-- The stage immediately before `s`: the last one that must have completed for `s` to have
started. `.read` is its own predecessor — it is the floor, reached as soon as there is any source
text at all. -/
def predecessor : Stage → Stage
  | .read | .lex => .read
  | .parse => .lex
  | .annotation => .parse
  | .desugar => .annotation
  | .resolve => .desugar
  | .typeCheck => .resolve
  | .wellFormedness => .typeCheck
  | .computable => .wellFormedness
  | .guarded => .computable
  | .network => .guarded
  | .go => .network

/-- Did a compile that reached `self` get at least as far as `target`? A plain `Bool` function
rather than an `LE`/`Decidable` instance pair: comparing two stages is a question about pipeline
progress, and nothing here wants order-class machinery. -/
def reaches (self target : Stage) : Bool := compare self target != .lt

end Stage

end
