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
  deriving DecidableEq, Repr, Inhabited, Ord, BEq

namespace Stage

/-- The `-d dump-<name>`/expectation-file spelling of a stage. -/
def name : Stage → String
  | .read => "read" | .lex => "lex" | .parse => "parse" | .annotation => "annotation"
  | .desugar => "desugar" | .resolve => "resolve" | .typeCheck => "typecheck"
  | .wellFormedness => "wellformedness" | .computable => "computable" | .guarded => "guarded"
  | .network => "network"

instance : ToString Stage := ⟨Stage.name⟩

/-- Every stage, in pipeline order. -/
def list : List Stage :=
  [.read, .lex, .parse, .annotation, .desugar, .resolve, .typeCheck, .wellFormedness,
   .computable, .guarded, .network]

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

/-- Did a compile that reached `self` get at least as far as `target`? A plain `Bool` function
rather than an `LE`/`Decidable` instance pair: comparing two stages is a question about pipeline
progress, and nothing here wants order-class machinery. -/
def reaches (self target : Stage) : Bool := compare self target != .lt

end Stage

end
