module

public import WellFormedness.WellScoped.TypedPlusCal
public import WellFormedness.WellScoped.CorePlusCal
public import WellFormedness.WellScoped.GuardedPlusCal

public section

/-!
  Well-scopedness — no duplicate names within one flat declaration list, and no name shadowing
  an already-in-scope one from an enclosing scope — across every `PlusCal` stage that has one:
  the **executable** check over `TypedPlusCal.Algorithm` (`.TypedPlusCal`, run by the driver),
  and a `Prop`-side counterpart per later stage (`.CorePlusCal`, `.GuardedPlusCal`), each
  authored fresh and not executed by anything — infrastructure for a future preservation lemma
  or proof precondition, one file per `PlusCal` stage.
-/

end
