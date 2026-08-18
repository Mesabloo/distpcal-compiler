module

public import Common.Position
public import Common.Diagnostics.Registry
import Mathlib.Data.String.Defs
public import Mathlib.Control.Monad.Writer
public import Colorized
meta import CustomPrelude

public section

open Colorized (Colorized)

/-- Anything can be colorized if we ignore the annotations. -/
instance (priority := low) {α} : Colorized α where
  colorize _ _ := id
  style _ := id

class CompilerDiagnostic (ε : Type _) (α : outParam (Type _)) [Colorized α] where
  isError : Bool
  posOf : ε → SourceSpan
  msgOf : ε → α
  hintsOf : ε → List α := λ _ ↦ []
  /-- The `-W<name>`/`-Wno-<name>` name this diagnostic is filtered under. Only meaningful for
  warnings — an error is never suppressed by `-W`, so its instance leaves this at the default. -/
  name : ε → String := λ _ ↦ ""
  /-- This diagnostic's stable code (`Common/Diagnostics/Registry.lean`), printed as
  `error[E0042]:` and taken as the identity a regression fixture or `fugue explain` names.
  Deliberately without a default: an instance must map *every* constructor to an entry, so adding
  a diagnostic without registering it fails to compile. -/
  code : ε → DiagnosticCode

/-- A pass with no warnings uses `MonadDiagnostic Empty ε m`. Lets `List Empty` still satisfy a
generic `[CompilerDiagnostic α String]` requirement; every field is `Empty.elim` since no `Empty`
value ever exists to apply it to. -/
instance : CompilerDiagnostic Empty String where
  isError := true
  posOf := Empty.elim
  msgOf := Empty.elim
  code := Empty.elim

/-- `Colorized.color`, but a no-op when `enabled` is `false` (`-fno-color`). Not `private`:
`Fugue.lean` reuses it for its `Built`/`Replayed` progress lines too. -/
def colorizeIf {α} [Colorized α] (enabled : Bool) (c : Colorized.Color) (x : α) : α :=
  if enabled then Colorized.color c x else x

/-- `Colorized.style`, but a no-op when `enabled` is `false` (`-fno-color`). Not `private`:
`Fugue.lean` reuses it too, for its `Built`/`Replayed`/`Failed` progress lines. -/
def styleIf {α} [Colorized α] (enabled : Bool) (s : Colorized.Style) (x : α) : α :=
  if enabled then Colorized.style s x else x

/-- Renders one diagnostic: an `error[E0042]:`-style header, the message and its hints, and the
offending source line with the span underlined. `colored := false` (driven by `-fno-color`) disables
ANSI styling. -/
@[nospecialize]
def CompilerDiagnostic.pretty {ε α : Type _} [Colorized α] [ToString α] [CompilerDiagnostic ε α] (err : ε) (source : List String.Slice) (colored : Bool := true) : String :=
  -- `error[E0042]:` / `warning[W0003]:` — the code is part of the header, so continuation lines
  -- and hints indent past all of it, not just past the severity word.
  let header := s!"{if CompilerDiagnostic.isError ε then "error" else "warning"}[{CompilerDiagnostic.code err}]"
  let color := if CompilerDiagnostic.isError ε then Colorized.Color.Red else .Yellow
  let headerPadding := String.replicate (header.length + 2) ' '
  let pos := CompilerDiagnostic.posOf err
  let n := pos.start.line
  let linePadding := String.replicate (n.repr.length + 2) ' '
  -- Degrade rather than panic on a line number this source doesn't have. A renderer is the last
  -- thing that should take the process down, and a span it cannot honour is a bug elsewhere
  -- (`SourceSpan.placeholder`'s line `1` is the sanctioned "no real position" value, and line `0`
  -- means a span was read off a node nothing ever registered) — this makes that bug show up as a
  -- blank quoted line, not as `PANIC at List.get!Internal`.
  let line := (source[n - 1]?).getD "".toSlice
  let startCol := pos.start.col
  let endCol := if pos.end.line > n then line.positions.length else pos.end.col
  let beginLine := line.take startCol
  let middleLine := line.drop startCol |>.take (endCol - startCol)
  let endLine := line.takeEnd (line.positions.length - endCol)
  s!"{colorizeIf colored color <| styleIf colored .Bold s!"{header}:"} {toString (CompilerDiagnostic.msgOf err) |>.replace "\n" s!"\n{headerPadding}"}{String.join ((CompilerDiagnostic.hintsOf err).map λ s ↦ s!"\n{headerPadding}" ++ (toString s).replace "\n" s!"\n{headerPadding}")}
{linePadding}|
 {n} | {beginLine}{colorizeIf colored color middleLine}{endLine}
{linePadding}|{String.replicate (startCol + 1) ' '}{colorizeIf colored color <| String.replicate (endCol - startCol) '^'}"

/-- The effects a diagnostics-producing pass needs: an always-growing `List α` of non-fatal
warnings (`MonadWriter`), plus `MonadExceptOf`'s throw/catch for a fatal `β`. The point isn't the
two constraints alone but their interaction, only actually guaranteed by `DiagT` below: the
accumulated `List α` survives a `throw`, unlike the ordinary `WriterT (List α) (ExceptT β ·)`
order, where a `throw` short-circuits before the writer's log is ever paired with anything. -/
class abbrev MonadDiagnostic (α β : outParam (Type _)) (m : Type _ → Type _) :=
  MonadWriter (List α) m, MonadExceptOf β m

/-- Emit a single warning. `MonadWriter.tell` wants a full `List α` (its monoid unit is `[]`),
but every call site only ever has one warning in hand at a time. -/
def warn {α β : Type _} {m : Type _ → Type _} [MonadDiagnostic α β m] (w : α) : m PUnit :=
  tell [w]

/-- The one concrete `MonadDiagnostic α β` instance that keeps the promise above: `Except β γ`
lives *inside* the pair as ordinary data, rather than as a monadic short-circuit wrapping the pair
from outside — so a `throw` is just `pure ([], .error e)`, and every warning already `tell`'d is
already in that `[]`, nothing lost. Also why `listen`/`pass` stay lossless, unlike the generic
`ExceptT ε N` composition, where `listen`'s `N (α × ω)` shape has nowhere to put `ω` once `α`
disappears on a throw. -/
@[expose] def DiagT (α β : Type _) (m : Type _ → Type _) (γ : Type _) : Type _ :=
  m (List α × Except β γ)

namespace DiagT

variable {α β γ : Type _} {m : Type _ → Type _}

/-- Unwrap a `DiagT` action down to the underlying `m`, always pairing every warning `tell`'d
against it with the final `Except`-wrapped result — regardless of which branch that result took.
The one place the main driver needs to reach into, to flush a pass's warnings whether or not that
pass ultimately threw. -/
@[expose] def run (x : DiagT α β m γ) : m (List α × Except β γ) := x

/-- Wrap an `m` action already in the right shape back up as a `DiagT`. -/
@[expose] def mk (x : m (List α × Except β γ)) : DiagT α β m γ := x

variable [Monad m]

instance : Monad (DiagT α β m) where
  pure a := DiagT.mk (pure ([], .ok a))
  bind x f :=
    DiagT.mk do
      let (w₁, r₁) ← DiagT.run x
      match r₁ with
      | .error e => pure (w₁, .error e)
      | .ok a => do
        let (w₂, r₂) ← DiagT.run (f a)
        pure (w₁ ++ w₂, r₂)

instance : MonadWriter (List α) (DiagT α β m) where
  tell w := DiagT.mk (pure (w, .ok ()))
  listen f :=
    DiagT.mk do
      let (w, r) ← DiagT.run f
      match r with
      | .error e => pure (w, .error e)
      | .ok a => pure (w, .ok (a, w))
  pass f :=
    DiagT.mk do
      let (w, r) ← DiagT.run f
      match r with
      | .error e => pure (w, .error e)
      | .ok (a, g) => pure (g w, .ok a)

instance : MonadExceptOf β (DiagT α β m) where
  throw e := DiagT.mk (pure ([], .error e))
  tryCatch x c :=
    DiagT.mk do
      let (w, r) ← DiagT.run x
      match r with
      | .error e => do
        let (w', r') ← DiagT.run (c e)
        pure (w ++ w', r')
      | .ok a => pure (w, .ok a)

/-- Lift any ambient `m` action in, unconditionally producing no warnings. -/
instance : MonadLift m (DiagT α β m) where
  monadLift x := DiagT.mk do
    let a ← x
    pure ([], .ok a)

/-- Lets `FlagsEnv`/`ResolutionStack` reach through whatever `DiagT` layer `compileModule` runs
at — lifts straight from the base `m`, same shape as the `MonadLift` instance above. -/
instance {ρ : Type _} [MonadReaderOf ρ m] : MonadReaderOf ρ (DiagT α β m) where
  read := DiagT.mk do
    let r ← (read : m ρ)
    pure ([], .ok r)

/-- Companion to the `MonadReaderOf` lift above — `ResolutionStack`'s push-on-recurse,
pop-on-return pattern (`withReader (mod.name :: ·)`) needs to reach through `DiagT` too. -/
instance {ρ : Type _} [MonadWithReaderOf ρ m] : MonadWithReaderOf ρ (DiagT α β m) where
  withReader f x := DiagT.mk (withReader f (DiagT.run x))

/-- Lifts `m`'s own state through `DiagT`, so any `[MonadStateOf _ m]`-generic instance picks it
up automatically without a dedicated `DiagT` instance. -/
instance {σ : Type _} [MonadStateOf σ m] : MonadStateOf σ (DiagT α β m) where
  get := DiagT.mk do
    let s ← (MonadStateOf.get : m σ)
    pure ([], .ok s)
  set s := DiagT.mk do
    MonadStateOf.set s
    pure ([], .ok ())
  modifyGet f := DiagT.mk do
    let a ← (MonadStateOf.modifyGet f : m _)
    pure ([], .ok a)

end DiagT

/-- Absorbs a self-contained sub-computation's diagnostics into the caller's ambient
`MonadDiagnostic α' β' m`: `tell`s `f`-mapped warnings, then `throw`s `g e` on `.error`, or returns
the value on `.ok`. `n` is `x`'s own base monad (`Id` for a pure runner, `IO`-flavored for a nested
recursive call), lifted into `m` via `MonadLiftT` so nothing about `x`'s concrete stack leaks into
the caller. Lets a caller `let`-bind straight through a sub-pass's result without unwrapping its
`DiagT`/`Except` by hand. -/
@[expose] def DiagT.lift {α α' β β' γ : Type _} {n m : Type _ → Type _} [Monad m] [MonadLiftT n m]
    [MonadDiagnostic α' β' m] (f : α → α') (g : β → β') (x : DiagT α β n γ) : m γ := do
  let (warnings, result) ← (liftM (DiagT.run x) : m (List α × Except β γ))
  tell (warnings.map f)
  match result with
  | .error e => throw (g e)
  | .ok a => pure a

end
