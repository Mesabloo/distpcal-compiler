module

public import Network2Go.Errors
public import Network2Go.Naming
public import Core.ComputableTLAPlus.Syntax

public section

/-!
  Compiling TLA⁺ types into Go types (thesis §7.2.1.1).

  Prior art got this for free by parameterizing its statement layer over TLA⁺ types directly;
  with `Core/Go/Syntax.lean` being real Go, the translation is this pass's own work (§5.7).

  - **Primitives go to the runtime's newtypes, not Go's builtins.** `Bool`/`Int`/`Str` compile to
    `tlaplus.Bool`/`tlaplus.Int`/`tlaplus.Str` rather than `bool`/`int`/`string`, because every
    value in generated code has to implement `Eq`/`Ord` and Go forbids implementing an interface
    for a type declared in another package. `Go.Typ`'s own `.bool`/`.int`/`.str` are still used
    by the pass, for the Go-level scaffolding a specification never sees — a branch function's
    `guard bool`, a scheduler's loop condition.
  - **Records compile to a struct with their fields sorted by name.** TLA⁺ records are unordered,
    so `[a ↦ 1, b ↦ 2]` and `[b ↦ 2, a ↦ 1]` are the same value and must compile to the same Go
    type; a struct's fields are ordered, so a canonical order has to be imposed. Sorting also
    makes the tuple encoding fall out unchanged, `proj1 … projn` already being in order.
  - **`Channel(τ)` has no case.** Channels are not first-class in Distributed PlusCal — one is
    never stored, passed, or placed in a data structure — so a channel type reaching this
    function means it turned up in an ordinary value position, which the well-formedness checks
    on channel declarations already rule out (`Typ.isChannelLike`, `WellFormedness/
    Declarations.lean`). The channel *declarations* themselves don't come through here: they
    become the process's `Network` parameter, built by the process-wiring compilation.
-/

namespace Network2Go

open ComputableTLAPlus

variable {m : Type → Type} [Monad m] [MonadDiagnostic Empty N2GError m]

/--
  Compiles a TLA⁺ type into its Go representation (§7.2.1.1).

  Fails only on types that cannot appear in a value position by the time this pass runs — see the
  module doc for `Channel(τ)`, and `Core/ComputableTLAPlus/Syntax.lean` for why no metavariable
  survives type checking.
-/
partial def compileTyp : Typ → m Go.Typ
  | .bool => return tlaplusTyp "Bool"
  | .int => return tlaplusTyp "Int"
  | .str => return tlaplusTyp "Str"
  | .set τ => return tlaplusTyp "Set" [← compileTyp τ]
  | .seq τ => return tlaplusTyp "Seq" [← compileTyp τ]
  -- A function is a lazy map rather than a Go `func`: its domain is a value the generated code
  -- inspects (`DOMAIN f`, and the domain check every application performs), which a `func` has
  -- no way to expose.
  | .function dom rng => return tlaplusTyp "LazyFunction" [← compileTyp dom, ← compileTyp rng]
  | .tuple τs => do
    let fields ← τs.zipIdx.mapM λ (τ, i) ↦ return (projName (i + 1), ← compileTyp τ)
    return .struct fields
  | .record fs => do
    let fields ← fs.mapM λ (x, τ) ↦ return (fieldName x, ← compileTyp τ)
    -- Canonical order, so that field order in the source cannot change the compiled type.
    return .struct (fields.mergeSort λ (x, _) (y, _) ↦ x ≤ y)
  -- An operator is not a value in TLA⁺ and has no domain to inspect, so unlike a function it is
  -- an ordinary Go function.
  | .operator τs τ => return .func (← τs.mapM compileTyp) [← compileTyp τ]
  -- A rigid type variable becomes a Go type parameter. Binding it is the enclosing definition's
  -- job (§7.2.2: type variables are propagated to the nearest enclosing function definition).
  | .var a => return .var (binderName a)
  -- An uninterpreted constant type is left with the name it had: the user supplies it when
  -- building a runnable system, the same boundary `CONSTANT` values themselves sit on.
  | .const c => return .named (definitionName (isLocal := false) c) []
  | .address => return commTyp "Address"
  | .channel τ =>
    throw (.internalInvariantViolated SourceSpan.placeholder
      s!"Channel({repr τ}) reached type compilation in a value position, but channels are not \
         first-class and should have been rejected by well-formedness checking")
  | .mvar n =>
    throw (.internalInvariantViolated SourceSpan.placeholder
      s!"unresolved metavariable ?{n} survived type checking")

end Network2Go

end
