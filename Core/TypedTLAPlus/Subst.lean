module

meta import CustomPrelude
public import Core.TypedTLAPlus.Syntax

@[expose] public section


/-!
  De Bruijn index manipulation for `TypedTLAPlus.Expression` under locally-nameless binding.

  `Origin.bound` uses standard de Bruijn indices: `.bound 0` is the nearest enclosing
  expression-level binder (`\A`/`\E`/`CHOOSE`, the two set-builders, `map'`, `fn`, and
  operator/function parameters). `Origin.free` names live in a separate namespace and never
  move an index.

  `liftBound` (shift the free `.bound` indices), `openVar` (a binder body's reference to its own
  binder becomes a free name) and `close` (its inverse) are one depth-tracking traversal,
  `mapVars`.
-/

namespace TypedTLAPlus

namespace Expression

/-- Rebuild every `.var` node knowing the number of expression-level binders enclosing it: `f k τ o
pos` is the replacement for a `.var τ o` sitting at binder depth `k`. Each binder arm recurses into
its scoped body at `k + 1`; domain and annotation positions stay at `k`. -/
partial def mapVars {α} (f : Nat → α → Origin → SourceSpan → Expression α) (k : Nat)
    (e : Expression α) : Expression α := match_source e with
  | .var τ o, pos => f k τ o pos
  | .nat n, pos => .nat n @@ pos
  | .str s, pos => .str s @@ pos
  | .true, pos => .true @@ pos
  | .false, pos => .false @@ pos
  | .opCall g es, pos => .opCall (mapVars f k g) (mapVars f k <$> es) @@ pos
  | .forall x ann dom body, pos =>
    .forall x ann (mapVars f k <$> dom) (mapVars f (k + 1) body) @@ pos
  | .exists x ann dom body, pos =>
    .exists x ann (mapVars f k <$> dom) (mapVars f (k + 1) body) @@ pos
  | .fforall x ann body, pos => .fforall x ann (mapVars f (k + 1) body) @@ pos
  | .eexists x ann body, pos => .eexists x ann (mapVars f (k + 1) body) @@ pos
  | .choose x ann dom body, pos =>
    .choose x ann (mapVars f k <$> dom) (mapVars f (k + 1) body) @@ pos
  | .set es τ, pos => .set (mapVars f k <$> es) τ @@ pos
  | .collect x ann dom pred, pos =>
    .collect x ann (mapVars f k dom) (mapVars f (k + 1) pred) @@ pos
  | .map' body x ann cod dom, pos =>
    .map' (mapVars f (k + 1) body) x ann cod (mapVars f k dom) @@ pos
  | .fnCall g fnTyp e', pos => .fnCall (mapVars f k g) fnTyp (mapVars f k e') @@ pos
  | .fn x ann cod dom body, pos =>
    .fn x ann cod (mapVars f k dom) (mapVars f (k + 1) body) @@ pos
  | .fnSet e₁ e₂, pos => .fnSet (mapVars f k e₁) (mapVars f k e₂) @@ pos
  | .record fs, pos => .record (Prod.map₃ id id (mapVars f k) <$> fs) @@ pos
  | .recordSet fs, pos => .recordSet (Prod.map₃ id id (mapVars f k) <$> fs) @@ pos
  | .except g τ upds, pos =>
    .except (mapVars f k g) τ
      (Bifunctor.bimap (·.map (Sum.map id (mapVars f k))) (mapVars f k) <$> upds) @@ pos
  | .recordAccess g nm, pos => .recordAccess (mapVars f k g) nm @@ pos
  | .tuple es, pos => .tuple (Bifunctor.bimap id (mapVars f k) <$> es) @@ pos
  | .seq es τ, pos => .seq (mapVars f k <$> es) τ @@ pos
  | .if e₁ e₂ e₃ τ, pos => .if (mapVars f k e₁) (mapVars f k e₂) (mapVars f k e₃) τ @@ pos
  | .case bs other τ, pos =>
    .case (Bifunctor.bimap (mapVars f k) (mapVars f k) <$> bs) (mapVars f k <$> other) τ @@ pos
  | .stutter e₁ e₂, pos => .stutter (mapVars f k e₁) (mapVars f k e₂) @@ pos
  | .mvar n e', pos => .mvar n (mapVars f k e') @@ pos

/-- Add `d` to every `.bound` index that refers past `e`'s own binders. -/
def liftBound {α} (d : Nat) (e : Expression α) : Expression α :=
  e.mapVars (λ k τ o pos ↦ match o with
    | .bound i => .var τ (.bound (if k ≤ i then i + d else i)) @@ pos
    | _ => .var τ o @@ pos) 0

/-- In a binder's body — already stripped of that binder — turn the reference to the removed
binder into the free name `name`, and shift every deeper free index down by one. -/
def openVar {α} (name : String) (e : Expression α) : Expression α :=
  e.mapVars (λ k τ o pos ↦ match o with
    | .bound i =>
      if i = k then .var τ (.free name) @@ pos
      else if k < i then .var τ (.bound (i - 1)) @@ pos
      else .var τ (.bound i) @@ pos
    | _ => .var τ o @@ pos) 0

/-- Bind every free occurrence of `name` as a new outermost `.bound`, shifting every deeper free
index up by one. Inverse of `openVar`. -/
def close {α} (name : String) (e : Expression α) : Expression α :=
  e.mapVars (λ k τ o pos ↦ match o with
    | .free n => if n = name then .var τ (.bound k) @@ pos else .var τ o @@ pos
    | .bound i => .var τ (.bound (if k ≤ i then i + 1 else i)) @@ pos
    | _ => .var τ o @@ pos) 0

end Expression

end TypedTLAPlus

end
