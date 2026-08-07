module

public import Guarded2Network.Errors
public import Guarded2Network.PlusCal
public import Guarded2Network.Lemmas

public section

/-!
  `Guarded2Network`'s entry point — `guarded.toNetwork` (`Guarded2Network/PlusCal.lean`), matching
  the `<InputType>.<verb>` convention `Typed2Computable`/`Computable2Guarded`/`WellFormedness`
  use. Unlike `Computable2Guarded` (four named subpasses, each in its own file), this pass isn't
  decomposed further — `Guarded2Network/PlusCal.lean` is the whole thing, so there's nothing else
  to re-export here beyond it and its own `G2NError` diagnostics type.
-/

end
