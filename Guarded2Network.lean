module

public import Guarded2Network.Errors
public import Guarded2Network.PlusCal

public section

/-!
  `Guarded2Network`'s entry point — `guarded.toNetwork` (`Guarded2Network/PlusCal.lean`), matching
  the `<InputType>.<verb>` convention `Typed2Computable`/`Computable2Guarded`/`WellFormedness`
  already use. Unlike `Computable2Guarded` (`𝒞_cflow`/`𝒞_par`/`𝒞_flat`/`𝒞_reord`, four named
  subpasses each in their own file), this pass isn't decomposed further — `Guarded2Network/
  PlusCal.lean` is the whole thing, so there's nothing else to re-export here beyond it and its own
  `G2NError` diagnostics type.
-/

end
