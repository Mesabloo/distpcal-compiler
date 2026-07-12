module

public import Typed2Computable.PlusCal
public import Core.TypedTLAPlus.Builtins
public import WellFormedness.Reachability
public import Elaborator

public section

/-!
  `TypedTLAPlus.Module.toComputable` — the `Typed2Computable` entry point. Given a checked,
  well-formed `TypedModule`, produces its computable fragment (`ComputableTLAPlus.Module
  ComputablePlusCal.Algorithm ComputableTLAPlus.Typ`):

  1. Collects the reachability closure from the embedded `pcalAlgorithm`
     (`Algorithm.collectReachable` below) — every constant/variable/operator/function
     transitively referenced, own-module or foreign. Foreign declarations are flattened straight
     into the output module's own `declarations₁` rather than kept separate (project owner's own
     call, `.claude/tasklist.md` task 8) — the checked module's own `EXTENDS` chain doesn't need
     to survive past this point, and every downstream pass only ever wants one self-contained
     module per compiled program.
  2. Drops every closure entry that resolved into a builtin/stdlib module
     (`TypedTLAPlus.builtinOpOf?`, keyed by the closure entry's own `(module, name)`) — project
     owner's own call: a builtin's "definition" is never actually used (`Driver/Builtins.lean`'s
     own module doc — backends replace every stdlib operator at code-generation time regardless
     of what its definition says), and may well use constructs this pass would otherwise reject
     (`fnSet`, an unbounded quantifier, …) despite no downstream consumer ever caring what its
     body says.
  3. Translates every remaining entry (`ResolvedDecl.toComputable` below) into one output
     declaration each — always exactly one `constants`/`variables`/`operator`/`function` node
     carrying just the one referenced `name` (project owner's own call: filter each original
     `CONSTANTS`/`VARIABLES` block down to just the referenced names, rather than re-emitting a
     whole multi-name block for one reference — `Decl.resolve` hands back the *whole* original
     node regardless of which one name triggered the match).
  4. Translates the algorithm itself (`Typed2Computable/PlusCal.lean`'s
     `TypedPlusCal.Algorithm.toComputable`).

  A module with no `pcalAlgorithm` at all produces an empty, algorithm-less computable module —
  same "no-op" shape `TypedTLAPlus.Module.checkWellFormed` already uses for the same case
  (`WellFormedness/WellFormedness.lean`); nothing here has anything to walk from.
-/

variable {m : Type → Type} [Monad m] [MonadExceptOf ComputableError m] [MonadForeignLookup m]

/-- Translates one `ReachabilityClosure` entry into the single declaration it contributes — `name`
comes from the entry's own `(module, name)` key (not stored in `ResolvedDecl` itself, which only
carries the whole resolved `Decl`), used both to pick out just this one name from a
`constants`/`variables` block and to re-name the translated `operator`/`function` (its own `Decl`
already carries the same name, but re-deriving it from the key rather than re-matching keeps this
independent of which of the two, structurally-identical fields the caller happened to use).

The `internalInvariantViolated` arms below are all defense-in-depth: `Decl.resolve`
(`WellFormedness/Reachability.lean`) only ever constructs a `ResolvedDecl.constant`/`.variable`
wrapping the exact `Decl.constants`/`.variables` node whose list contains `name`, and an
`.operatorOrFunction` wrapping exactly the `Decl.operator`/`.function` node named `name` — so none
of these arms should be reachable, but no proof of that exists yet (same reasoning as
`Typed2Computable/Errors.lean`'s own `internalInvariantViolated`), and `SourceSpan.placeholder` is
the same "no real position to report against" placeholder `Common/Position.lean` defines for
exactly this kind of diagnostic. -/
def ResolvedDecl.toComputable (name : String) :
    ResolvedDecl → m (ComputableTLAPlus.Declaration ComputableTLAPlus.Typ)
  | .constant (.constants xs) => match xs.find? (·.1 == name) with
    | some (_, τ) => pure (.constants [(name, τ)])
    | none => throw (.internalInvariantViolated SourceSpan.placeholder
        s!"reachability closure entry for constant '{name}' whose own resolved Decl.constants list didn't contain it")
  | .constant _ => throw (.internalInvariantViolated SourceSpan.placeholder
      "reachability closure .constant entry whose Decl wasn't itself a Decl.constants node")
  | .variable (.variables xs) => match xs.find? (·.1 == name) with
    | some (_, τ) => pure (.variables [(name, τ)])
    | none => throw (.internalInvariantViolated SourceSpan.placeholder
        s!"reachability closure entry for variable '{name}' whose own resolved Decl.variables list didn't contain it")
  | .variable _ => throw (.internalInvariantViolated SourceSpan.placeholder
      "reachability closure .variable entry whose Decl wasn't itself a Decl.variables node")
  | .operatorOrFunction (.operator ann _ params _) body =>
    (.operator ann name params ·) <$> body.toComputable
  | .operatorOrFunction (.function ann _ params _) body => do
    let params' ← params.mapM λ (pname, dom) ↦ (pname, ·) <$> dom.toComputable
    (.function ann name params' ·) <$> body.toComputable
  | .operatorOrFunction _ _ => throw (.internalInvariantViolated SourceSpan.placeholder
      "reachability closure .operatorOrFunction entry whose Decl was neither .operator nor .function")

/-- Runs the shared reachability walk (`WellFormedness/Reachability.lean`) from `algo`, with no-op
`visitStatement`/`visitExpr` callbacks — unlike `WellFormedness/Restrictions.lean`'s own use of the
same walk, `Typed2Computable` wants none of its checks (already run and passed, earlier in the
pipeline), only the `ReachabilityClosure` side effect the walk accumulates. `.run`, not `.run'`
(`Restrictions.lean`'s own choice) — the whole point here is to keep the closure. -/
def TypedPlusCal.Algorithm.collectReachable (currentModule : String) (ownDecls : List Decl)
    (algo : TypedPlusCal.Algorithm) : m ReachabilityClosure := do
  let go : StateT ReachabilityClosure m Unit :=
    TypedPlusCal.Algorithm.walkReachable (λ _ ↦ pure ()) (λ _ _ ↦ pure ()) currentModule ownDecls algo
  Prod.snd <$> go.run {}

/-- The `Typed2Computable` entry point — see the module doc above. -/
def TypedTLAPlus.Module.toComputable (mod : TypedModule) :
    m (ComputableTLAPlus.Module ComputablePlusCal.Algorithm ComputableTLAPlus.Typ) :=
  match mod.pcalAlgorithm with
  | none => pure {
      name := mod.name, «extends» := mod.extends
      declarations₁ := [], pcalAlgorithm := none, declarations₂ := []
    }
  | some algo => do
    let closure ← TypedPlusCal.Algorithm.collectReachable mod.name (mod.declarations₁ ++ mod.declarations₂) algo
    let declarations₁ ← closure.toList.filterMapM λ ((declModule, name), resolved) ↦
      if (TypedTLAPlus.builtinOpOf? (.module declModule) name).isSome then pure none
      else some <$> ResolvedDecl.toComputable name resolved
    let algo' ← TypedPlusCal.Algorithm.toComputable algo
    pure {
      name := mod.name, «extends» := mod.extends
      declarations₁, pcalAlgorithm := some algo', declarations₂ := []
    }

end
