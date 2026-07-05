import Core.TypedTLAPlus.Syntax
import Core.CorePlusCal.Syntax

/-!
  The output of PlusCal statement checking (§5.3, thesis §3.1.5) — `CorePlusCal.Statement`/
  `Block`/`Branches`/`Declarations`/`Process`/`Algorithm`, reused as-is rather than given a fresh
  AST: per the thesis, statement checking "produces no type information" of its own — the
  statement *shape* never changes, only its embedded expressions do (`CoreTLAPlus.Expression` →
  checked `TypedTLAPlus.Expression`), and every annotation slot (`α`) goes from statement
  desugaring's still-possibly-absent one to a real `TypedTLAPlus.Typ`.

  `CorePlusCal`'s own module doc already explains why `α` is one shared parameter across every
  annotation-carrying slot (`Statement.with`'s bound-variable annotation, `Declarations.variables`/
  `channels`/`fifos`, `MulticastFilter.binds`) rather than several independently-typed ones: it's
  what lets `Process`/`Algorithm` stay ordinary two-parameter `Bifunctor`/`Bitraversable`
  instances, with one walk covering every slot uniformly, no special-casing. That reasoning still
  holds at `α := TypedTLAPlus.Typ` — every slot ends up with a real type, populated as: a
  variable's own declared/inferred type (`Declarations.variables`, in either a process's
  `localState` or the algorithm's `globalState`); a `with`-bound variable's type
  (`Statement.with`); a channel/FIFO's *element* type `τ` — not the wrapped `Channel(τ)`, since
  the channel-ness is already implied structurally by being a `channels`/`fifos` entry at all, so
  the checker stores just `τ` (`Declarations.channels`/`fifos`); a multicast bind's type
  (`MulticastFilter.binds`), matching `with`'s own convention. Confirmed with the project owner:
  a process-local `Declarations`' `channels`/`fifos` lists are typically just empty (channels and
  FIFOs are almost always declared globally), but the shared `Declarations` shape still carries
  the slot regardless, rather than splitting "local" and "global" declarations into two different
  structures.
-/

namespace TypedPlusCal

/-- Checked PlusCal expressions — always `TypedTLAPlus.Expression` at the checker's own `Typ`. -/
abbrev Expression := TypedTLAPlus.Expression TypedTLAPlus.Typ

/-- `CorePlusCal.Ref`, checked. -/
abbrev Ref := CorePlusCal.Ref Expression
/-- `CorePlusCal.Statement`, checked. -/
abbrev Statement (terminal : Bool) := CorePlusCal.Statement TypedTLAPlus.Typ Expression terminal
/-- `CorePlusCal.Block`, checked. -/
abbrev Block (terminal : Bool) := CorePlusCal.Block TypedTLAPlus.Typ Expression terminal
/-- `CorePlusCal.Branches`, checked. -/
abbrev Branches (terminal : Bool) := CorePlusCal.Branches TypedTLAPlus.Typ Expression terminal
/-- `SurfacePlusCal.MulticastFilter`, checked. -/
abbrev MulticastFilter := SurfacePlusCal.MulticastFilter TypedTLAPlus.Typ Expression
/-- `CorePlusCal.Declarations`, checked. -/
abbrev Declarations := CorePlusCal.Declarations TypedTLAPlus.Typ Expression
/-- `CorePlusCal.Process`, checked. -/
abbrev Process := CorePlusCal.Process TypedTLAPlus.Typ Expression
/-- `CorePlusCal.Algorithm`, checked — the type finally handed to `Typed2Guarded`. -/
abbrev Algorithm := CorePlusCal.Algorithm TypedTLAPlus.Typ Expression

end TypedPlusCal
