module

public import Network2Go.Errors
public import Network2Go.Naming
public import Network2Go.Typ

public section

/-!
  `Network2Go`'s entry point — `network.toGo` (`Network2Go/PlusCal.lean`), matching the
  `<InputType>.<verb>` convention the other passes use. Only the pass's `N2GError` diagnostics type
  exists so far; the compilation modules are re-exported here as they land.
-/

end
