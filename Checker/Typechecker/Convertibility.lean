import PlusCalCompiler.Passes.AnnotationChecker.Typechecker.Monad


partial def conv? : InternalType → InternalType → TC Bool
  | .typ τ, .mvar n | .mvar n, .typ τ => do
    if let .some τ' ← TC.mvarSolved? n then
      conv? τ τ'
    else
      if let .some τ' ← assigned? n then
        -- FIXME: if `τ'` is a metavariable, `conv?` may loop indefinitely.
        -- Typically, if `τ' = .mvar n` then this is guaranteed to loop forever.
        -- But this should not happen...
        conv? τ τ'
      else
        let _ ← assignMVar n (InternalType.typ τ)
        return true
  | .mvar m, .mvar n => sorry
  | _, _ => sorry



infix:60 " ≅ " => conv?
