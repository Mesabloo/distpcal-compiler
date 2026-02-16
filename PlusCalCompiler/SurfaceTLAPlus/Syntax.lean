import PlusCalCompiler.Position
import PlusCalCompiler.SurfaceTLAPlus.Tokens
import Mathlib.Control.Bifunctor
import Mathlib.Control.Traversable.Basic
import Mathlib.Control.Traversable.Instances
import Mathlib.Control.Bitraversable.Basic
import Mathlib.Control.Bitraversable.Instances
import Mathlib.Control.Functor
import Mathlib.Logic.Function.Defs
import Extra.Prod

namespace SurfaceTLAPlus
  abbrev 𝒱 := String

  /-- TLA⁺ types, in the [same format as Apalache](https://apalache-mc.org/docs/adr/002adr-types.html). -/
  inductive Typ.{u} : Type u
    /-- `Bool` -/
    | bool
    /-- `Int` -/
    | int
    /-- `Str` -/
    | str
    /-- `τ -> τ` -/
    | function (_ _ : Typ)
    /-- `Set(τ)` -/
    | set (_ : Typ)
    /-- `Seq(τ)` -/
    | seq (_ : Typ)
    /-- `<<τ₁, …, τₙ>>` -/
    | tuple (_ : List Typ)
    /-- `(τ₁, …, τₙ) => τₙ₊₁` -/
    | operator (_ : List Typ) (_ : Typ)
    /-- `a` -/
    | var (_ : 𝒱)
    /-- `CONST` -/
    | const (_ : 𝒱)
    -- polyrecord/polyvariants? https://apalache-mc.org/docs/adr/002adr-types.html#ts12
    | record (_ : List (𝒱 × Typ))
    --------------------
    -- PlusCal specific types
    /-- `Channel(τ)` -/
    | channel (_ : Typ)
    | address
    deriving Repr, Inhabited, BEq

  partial instance : DecidableEq Typ :=
    let rec go (τ τ' : Typ) : Decidable (τ = τ') := match τ, τ' with
      -- Decide equality there
      | .bool, .bool | .int, .int | .str, .str => isTrue rfl
      | .function dom rng, .function dom' rng' =>
        match go dom dom', go rng rng' with
        | .isTrue h₁, .isTrue h₂ => isTrue (by rw [h₁, h₂])
        | .isTrue h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
        | .isFalse h₁, .isTrue h₂ => isFalse λ h' ↦ by injections; contradiction
        | .isFalse h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
      | .set τ, .set τ' | .seq τ, .seq τ' | .channel τ, .channel τ' =>
        match go τ τ' with
        | isTrue h => isTrue (by rw [h])
        | isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      | .tuple τs, .tuple τs' =>
        match @List.hasDecEq _ go τs τs' with
        | .isTrue h => isTrue (by rw [h])
        | .isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      | .operator τs τ, .operator τs' τ' =>
        match @List.hasDecEq _ go τs τs', go τ τ' with
        | .isTrue h₁, .isTrue h₂ => isTrue (by rw [h₁, h₂])
        | .isTrue h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; absurd h₁; trivial
        | .isFalse h₁, .isTrue h₂ => isFalse λ h' ↦ by injections; absurd h₁; trivial
        | .isFalse h₁, .isFalse h₂ => isFalse λ h' ↦ by injections; absurd h₁; trivial
      | .var v, .var v' | .const v, .const v' =>
        if h : v = v' then
          isTrue (by rw [h])
        else
          isFalse λ h' ↦ by injections; absurd h; trivial
      | .record fs, .record fs' =>
        let Prod.hasDecEq {α β : Type _} [DecidableEq α] [DecidableEq β] : DecidableEq (α × β) := inferInstance

        match @List.hasDecEq _ (@Prod.hasDecEq _ _ inferInstance go) fs fs' with
        | .isTrue h => isTrue (by rw [h])
        | .isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      | .address, .address => isTrue rfl
      -- Other shit cases that need to be explicitly defined, unfortunately
      | .bool, .int | .bool, .str | .bool, .function .. | .bool, .set .. | .bool, .seq .. | .bool, .channel ..
      | .bool, .tuple .. | .bool, .operator .. | .bool, .var .. | .bool, .const .. | .bool, .record .. | .bool, .address => isFalse nofun
      | .int, .bool | .int, .str | .int, .function .. | .int, .set .. | .int, .seq .. | .int, .channel ..
      | .int, .tuple .. | .int, .operator .. | .int, .var .. | .int, .const .. | .int, .record .. | .int, .address => isFalse nofun
      | .str, .bool | .str, .int | .str, .function .. | .str, .set .. | .str, .seq .. | .str, .channel ..
      | .str, .tuple .. | .str, .operator .. | .str, .var .. | .str, .const .. | .str, .record .. | .str, .address => isFalse nofun
      | .function .., .bool | .function .., .int | .function .., .str | .function .., .set .. | .function .., .seq ..
      | .function .., .channel .. | .function .., .tuple .. | .function .., .operator .. | .function .., .var ..
      | .function .., .const .. | .function .., .record .. | .function .., .address => isFalse nofun
      | .set .., .bool | .set .., .int | .set .., .str | .set .., .function .. | .set .., .seq ..
      | .set .., .channel .. | .set .., .tuple .. | .set .., .operator .. | .set .., .var ..
      | .set .., .const .. | .set .., .record .. | .set .., .address => isFalse nofun
      | .seq .., .bool | .seq .., .int | .seq .., .str | .seq .., .function .. | .seq .., .set ..
      | .seq .., .channel .. | .seq .., .tuple .. | .seq .., .operator .. | .seq .., .var ..
      | .seq .., .const .. | .seq .., .record .. | .seq .., .address => isFalse nofun
      | .channel .., .bool | .channel .., .int | .channel .., .str | .channel .., .function .. | .channel .., .set ..
      | .channel .., .seq .. | .channel .., .tuple .. | .channel .., .operator .. | .channel .., .var ..
      | .channel .., .const .. | .channel .., .record .. | .channel .., .address => isFalse nofun
      | .tuple .., .bool | .tuple .., .int | .tuple .., .str | .tuple .., .function .. | .tuple .., .set ..
      | .tuple .., .seq .. | .tuple .., .channel .. | .tuple .., .operator .. | .tuple .., .var ..
      | .tuple .., .const .. | .tuple .., .record .. | .tuple .., .address => isFalse nofun
      | .operator .., .bool | .operator .., .int | .operator .., .str | .operator .., .function .. | .operator .., .set ..
      | .operator .., .seq .. | .operator .., .channel .. | .operator .., .tuple .. | .operator .., .var ..
      | .operator .., .const .. | .operator .., .record .. | .operator .., .address => isFalse nofun
      | .var .., .bool | .var .., .int | .var .., .str | .var .., .function .. | .var .., .set ..
      | .var .., .seq .. | .var .., .channel .. | .var .., .tuple .. | .var .., .operator ..
      | .var .., .const .. | .var .., .record .. | .var .., .address => isFalse nofun
      | .const .., .bool | .const .., .int | .const .., .str | .const .., .function .. | .const .., .set ..
      | .const .., .seq .. | .const .., .channel .. | .const .., .tuple .. | .const .., .operator ..
      | .const .., .var .. | .const .., .record .. | .const .., .address => isFalse nofun
      | .record .., .bool | .record .., .int | .record .., .str | .record .., .function .. | .record .., .set ..
      | .record .., .seq .. | .record .., .channel .. | .record .., .tuple .. | .record .., .operator ..
      | .record .., .var .. | .record .., .const .. | .record .., .address => isFalse nofun
      | .address, .bool | .address, .int | .address, .str | .address, .function .. | .address, .set ..
      | .address, .seq .. | .address, .channel .. | .address, .tuple .. | .address, .operator ..
      | .address, .var .. | .address, .const .. | .address, .record .. => isFalse nofun
    go

  partial instance : ToString Typ where
    toString :=
      let rec go : Typ → String
        | .bool => "Bool"
        | .int => "Int"
        | .str => "Str"
        | .address => "Address"
        | .function τ₁ τ₂ => s!"({go τ₁}) -> {go τ₂}"
        | .set τ => s!"Set({go τ})"
        | .seq τ => s!"Seq({go τ})"
        | .tuple τs => s!"<<{String.intercalate ", " (τs.map go)}>>"
        | .operator τs τ => s!"({String.intercalate ", " (τs.map go)}) => {go τ}"
        | .var v => v
        | .const v => v
        | .record fs => "{" ++ String.intercalate ", " (fs.map λ ⟨v, τ⟩ ↦ v ++ " : " ++ go τ) ++ "}"
        | .channel τ => s!"Channel({go τ})"
      go

  /- TLA+: https://lamport.azurewebsites.net/tla/TLAPlus2Grammar.tla -/
  /- See also page 268 of the book "Specifying Systems". -/

  /--
    Represents groups of variables bound in quantifiers (e.g. `\A`).
  -/
  inductive QuantifierBound (𝒱 : Type) (α β : Type) : Type
    /-- `x ∈ A` -/
    | var : List α → 𝒱 → β → QuantifierBound 𝒱 α β
    /-- `⟨x, y, ⋯, z⟩ ∈ A` -/
    | varTuple : List (List α × 𝒱) → β → QuantifierBound 𝒱 α β
    /-- `x, y, ⋯, z ∈ A` -/
    | vars : List (List α × 𝒱) → β → QuantifierBound 𝒱 α β
    deriving Repr, DecidableEq, BEq

  protected def QuantifierBound.bimap {α β γ δ 𝒱 : Type _} (f : α → γ) (g : β → δ) : QuantifierBound 𝒱 α β → QuantifierBound 𝒱 γ δ
    | .var anns v x => .var (f <$> anns) v (g x)
    | .vars vs x => .vars (Bifunctor.fst (f <$> ·) <$> vs) (g x)
    | .varTuple vs x => .varTuple (Bifunctor.fst (f <$> ·) <$> vs) (g x)

  instance {𝒱} : Bifunctor (QuantifierBound 𝒱) where
    bimap := QuantifierBound.bimap

  protected def QuantifierBound.bitraverse {G : Type _ → Type _} [Applicative G] {α β γ δ 𝒱} (f : α → G γ) (g : β → G δ) : QuantifierBound 𝒱 α β → G (QuantifierBound 𝒱 γ δ)
    | .var anns v x => (.var · v ·) <$> traverse f anns <*> g x
    | .vars vs x => .vars <$> traverse (bitraverse (traverse f) pure) vs <*> g x
    | .varTuple vs x => .varTuple <$> traverse (bitraverse (traverse f) pure) vs <*> g x

  instance {𝒱 : Type } : Bitraversable (QuantifierBound 𝒱) where
    bitraverse := QuantifierBound.bitraverse

  /--
    This type represents either a single variable `x` or a tuple of variables `⟨x, y, …, z⟩`.
  -/
  def IdentifierOrTuple (𝒱 : Type _) := 𝒱 ⊕ List 𝒱

  instance {𝒱} [Repr 𝒱] : Repr (IdentifierOrTuple 𝒱) := inferInstanceAs (Repr (_ ⊕ _))

  instance {𝒱} [DecidableEq 𝒱] : DecidableEq (IdentifierOrTuple 𝒱) := inferInstanceAs (DecidableEq (_ ⊕ _))

  instance : Functor IdentifierOrTuple where
    map f
      | .inl x => .inl (f x)
      | .inr xs => .inr (f <$> xs)

  instance : Traversable IdentifierOrTuple where
    traverse f
      | .inl x => .inl <$> f x
      | .inr xs => .inr <$> traverse f xs

  /--
    General annotations, as [supported in Apalache](https://apalache-mc.org/docs/adr/004adr-annotations.html).
  -/
  abbrev CommentAnnotation := 𝒱 × List (String ⊕ Int ⊕ Bool ⊕ 𝒱)

  -- TODO: support qualified identifiers and operators

  /--
    The inductive type describing TLA⁺ expressions as accepted syntactically.

    The `α` parameter is used to make the type of comment annotations generic.
  -/
  inductive Expression (α : Type) : Type
    /-- A TLA+ (unqualified) identifier. -/
    | var : 𝒱 → Expression α
    /-- An operator call `f(e₁, …, eₙ)`. -/
    | opCall : Located (Expression α) → List (Located (Expression α)) → Expression α
    /-- A prefix operator call. -/
    | prefixCall : Located PrefixOperator → Located (Expression α) → Expression α
    /-- An infix operator call. -/
    | infixCall : Located (Expression α) → Located InfixOperator → Located (Expression α) → Expression α
    /-- A postfix operator call. -/
    | postfixCall : Located (Expression α) → Located PostfixOperator → Expression α
    /-- A simple parenthesized expression. -/
    | parens : Located (Expression α) → Expression α
    /-- Bounded universal quantification `\A q \in A : e`. -/
    | bforall : List (QuantifierBound (Located 𝒱) α (Located (Expression α))) → Located (Expression α) → Expression α
    /-- Bounded existential quantification `\E q \in A : p`. -/
    | bexists : List (QuantifierBound (Located 𝒱) α (Located (Expression α))) → Located (Expression α) → Expression α
    /-- Unbounded universal quantification `\A x, y, …, z : p`. -/
    | forall : List (Located 𝒱) → Located (Expression α) → Expression α
    /-- Unbounded existential quantification `\E x, y, …, z : p`. -/
    | exists : List (Located 𝒱) → Located (Expression α) → Expression α
    /-- Temporal universal quantification `\AA x, y, …, z : p`. -/
    | fforall : List (Located 𝒱) → Located (Expression α) → Expression α
    /-- Temporal existential quantification `\EE x, y, …, z : p`. -/
    | eexists : List (Located 𝒱) → Located (Expression α) → Expression α
    /-- Hilbert's epsilon operator `CHOOSE x \in A : p`. -/
    | choose : IdentifierOrTuple (Located 𝒱) → Option (Located (Expression α)) → Located (Expression α) → Expression α
    /-- A literal set `{e₁, …, eₙ}`. -/
    | set : List (Located (Expression α)) → Expression α
    /-- Set collection/filtering `{x \in A : p}`. -/
    | collect : IdentifierOrTuple (Located 𝒱) → Located (Expression α) → Located (Expression α) → Expression α
    /-- The image of a function by a set `{e : x \in A}`. -/
    | map' : Located (Expression α) → List (QuantifierBound (Located 𝒱) α (Located (Expression α))) → Expression α
    /-- A function call `f[e₁, …, eₙ]`. -/
    | fnCall : Located (Expression α) → List (Located (Expression α)) → Expression α
    /-- A function literal `[x \in A, …, z \in B ↦ e]`. -/
    | fn : List (QuantifierBound (Located 𝒱) α (Located (Expression α))) → Located (Expression α) → Expression α
    /-- The set of all functions from a given domain to a given codomain `[A -> B]`. -/
    | fnSet : Located (Expression α) → Located (Expression α) → Expression α
    /-- The literal record `[a |-> e₁, …, z |-> eₙ]`. -/
    | record : List (List α × Located 𝒱 × Located (Expression α)) → Expression α
    /-- The set of all records whose fields are in the given sets `[a : A, …, z : Z]`. -/
    | recordSet : List (List α × Located 𝒱 × Located (Expression α)) → Expression α
    /-- Function update `[f EXCEPT ![e₁] = e₂]`. -/
    | except : Located (Expression α) → List (List (Located 𝒱 ⊕ List (Located (Expression α))) × Located (Expression α)) → Expression α
    /-- Record access `r.x`. -/
    | recordAccess : Located (Expression α) → Located 𝒱 → Expression α
    /-- A literal tuple `<<e₁, …, eₙ>>`. -/
    | tuple : List (Located (Expression α)) → Expression α
    /-- Conditional expression `IF e₁ THEN e₂ ELSE e₃`. -/
    | if : Located (Expression α) → Located (Expression α) → Located (Expression α) → Expression α
    /-- Case distinction `CASE p₁ -> e₁ [] … [] OTHER -> eₙ₊₁`. -/
    | case : List (Located (Expression α) × Located (Expression α)) → Option (Located (Expression α)) → Expression α
    -- TODO: to be able to define `LET`, we need to make `Expression` mutual with `Declaration`…
    /-- Conjunction `P /\ … /\ R`. -/
    | conj : List (Located (Expression α)) → Expression α
    /-- Disjunction `P \/ … \/ R`. -/
    | disj : List (Located (Expression α)) → Expression α
    /-- A natural number. -/
    | nat : String → Expression α
    /-- A literal string. -/
    | str : String → Expression α
    /-- `@` -/
    | at : Expression α
    /-- `[A]_e` -/
    | stutter : Located (Expression α) → Located (Expression α) → Expression α
    -- WF_ / SF_
    -- TODO: other temporal and action operators
    -- TODO: module instances
    deriving Repr, Inhabited

  -- Enjoy this neat trick.
  section
    /-
      __How this works:__

      We define a new local instance for comparaison within `Located`, which basically only
      compares the data carried, not the actual positions.
      Then we derive `BEq` for `Expression`, which takes this local instance to compare all values
      stored within other expressions.
      As such, this means that we are traversing (and checking for equality) the whole expression tree
      while completely ignoring the (irrelevant for this) positions of the nodes.
    -/
    local instance (priority := high) {α} [BEq α] : BEq (Located α) := open Function in ⟨BEq.beq on Located.data⟩
    deriving instance BEq for Expression

    protected def Expression.stripPosEq {α} [BEq α] (e₁ e₂ : Located (Expression α)) : Bool := e₁ == e₂
  end
  /-
    Then, outside the section (where the local instance is unavailable), re-derive `BEq` for `Expression`.
    Here, this will take the old instance of `BEq` for `Located`, which also compares positions of the nodes.
  -/
  deriving instance BEq for Expression

  /-
    We can see here that our trick worked: the first `#guard` successfully compares expressions with different
    positions, while the second fails to do so.
  -/
  #guard Expression.stripPosEq (α := Empty) ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, .parens ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, .var "x"⟩⟩ ⟨⟨⟨10, 8⟩, ⟨10, 9⟩⟩, .parens ⟨⟨⟨10, 8⟩, ⟨10, 9⟩⟩, .var "x"⟩⟩
  @[irreducible, noinline, deprecated Expression.stripPosEq (since := "forever")]
  private def Expression.stripPosEq' {α} [BEq α] (e₁ e₂ : Located (Expression α)) : Bool := e₁ == e₂
  set_option linter.deprecated false in
  #guard !Expression.stripPosEq' (α := Empty) ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, .parens ⟨⟨⟨0, 0⟩, ⟨0, 0⟩⟩, .var "x"⟩⟩ ⟨⟨⟨10, 8⟩, ⟨10, 9⟩⟩, .parens ⟨⟨⟨10, 8⟩, ⟨10, 9⟩⟩, .var "x"⟩⟩

  -- TODO: prove termination, at some point
  protected partial def Expression.map {α β} (f : α → β) : Expression α → Expression β
    | .var v => .var v
    | .nat n => .nat n
    | .str s => .str s
    | .at => .at
    | .opCall v es => .opCall (Expression.map f <$> v) ((Expression.map f <$> ·) <$> es)
    | .prefixCall op e => .prefixCall op (Expression.map f <$> e)
    | .infixCall e₁ op e₂ => .infixCall (Expression.map f <$> e₁) op (Expression.map f <$> e₂)
    | .postfixCall e op => .postfixCall (Expression.map f <$> e) op
    | .parens e => .parens (Expression.map f <$> e)
    | .bforall qs e => .bforall (bimap f (Expression.map f <$> ·) <$> qs) (Expression.map f <$> e)
    | .bexists qs e => .bexists (bimap f (Expression.map f <$> ·) <$> qs) (Expression.map f <$> e)
    | .forall vs e => .forall vs (Expression.map f <$> e)
    | .exists vs e => .exists vs (Expression.map f <$> e)
    | .fforall vs e => .fforall vs (Expression.map f <$> e)
    | .eexists vs e => .eexists vs (Expression.map f <$> e)
    | .choose vs e₁ e₂ => .choose vs ((Expression.map f <$> ·) <$> e₁) (Expression.map f <$> e₂)
    | .set es => .set ((Expression.map f <$> ·) <$> es)
    | .collect vs e₁ e₂ => .collect vs (Expression.map f <$> e₁) (Expression.map f <$> e₂)
    | .map' e qs => .map' (Expression.map f <$> e) (bimap f (Expression.map f <$> ·) <$> qs)
    | .fnCall e es => .fnCall (Expression.map f <$> e) ((Expression.map f <$> ·) <$> es)
    | .fn qs e => .fn (bimap f (Expression.map f <$> ·) <$> qs) (Expression.map f <$> e)
    | .fnSet e₁ e₂ => .fnSet (Expression.map f <$> e₁) (Expression.map f <$> e₂)
    | .record fs => .record (Prod.map₃ (f <$> ·) id (Expression.map f <$> ·) <$> fs)
    | .recordSet fs => .recordSet (Prod.map₃ (f <$> ·) id (Expression.map f <$> ·) <$> fs)
    | .except e upds => .except (Expression.map f <$> e) (bimap (Bifunctor.snd ((Expression.map f <$> ·) <$> ·) <$> ·) (Expression.map f <$> ·) <$> upds)
    | .recordAccess e v => .recordAccess (Expression.map f <$> e) v
    | .tuple es => .tuple ((Expression.map f <$> ·) <$> es)
    | .if e₁ e₂ e₃ => .if (Expression.map f <$> e₁) (Expression.map f <$> e₂) (Expression.map f <$> e₃)
    | .case es e => .case (bimap (Expression.map f <$> ·) (Expression.map f <$> ·) <$> es) ((Expression.map f <$> ·) <$> e)
    | .conj es => .conj ((Expression.map f <$> ·) <$> es)
    | .disj es => .disj ((Expression.map f <$> ·) <$> es)
    | .stutter e₁ e₂ => .stutter (Expression.map f <$> e₁) (Expression.map f <$> e₂)

  instance : Functor Expression where
    map := Expression.map

  local instance {F : Type _ → Type _} [Applicative F] {α} : Inhabited (F (Expression α)) := ⟨pure .at⟩ in
  -- TODO: prove termination at some point
  protected partial def Expression.traverse {F : Type _ → Type _} [Applicative F] {α β} (f : α → F β) : Expression α → F (Expression β)
    | .var v => pure <| .var v
    | .nat n => pure <| .nat n
    | .str s => pure <| .str s
    | .at => pure .at
    | .opCall e es =>
        .opCall <$> traverse (Expression.traverse f) e
                <*> traverse (traverse (Expression.traverse f)) es
    | .prefixCall op e =>
        .prefixCall op <$> traverse (Expression.traverse f) e
    | .infixCall e₁ op e₂ =>
        (.infixCall · op ·) <$> traverse (Expression.traverse f) e₁
                            <*> traverse (Expression.traverse f) e₂
    | .postfixCall e op =>
        (.postfixCall · op) <$> traverse (Expression.traverse f) e
    | .parens e =>
        .parens <$> traverse (Expression.traverse f) e
    | .bforall qs e =>
        .bforall <$> traverse (bitraverse f (traverse (Expression.traverse f))) qs
                 <*> traverse (Expression.traverse f) e
    | .bexists qs e =>
        .bexists <$> traverse (bitraverse f (traverse (Expression.traverse f))) qs
                 <*> traverse (Expression.traverse f) e
    | .forall vs e =>
        .forall vs <$> traverse (Expression.traverse f) e
    | .exists vs e =>
        .exists vs <$> traverse (Expression.traverse f) e
    | .fforall vs e =>
        .fforall vs <$> traverse (Expression.traverse f) e
    | .eexists vs e =>
        .eexists vs <$> traverse (Expression.traverse f) e
    | .choose vs e₁ e₂ =>
        .choose vs <$> traverse (traverse (Expression.traverse f)) e₁
                   <*> traverse (Expression.traverse f) e₂
    | .set es =>
        .set <$> traverse (traverse (Expression.traverse f)) es
    | .collect vs e₁ e₂ =>
        .collect vs <$> traverse (Expression.traverse f) e₁
                    <*> traverse (Expression.traverse f) e₂
    | .map' e qs =>
        .map' <$> traverse (Expression.traverse f) e
              <*> traverse (bitraverse f (traverse (Expression.traverse f))) qs
    | .fnCall e es =>
        .fnCall <$> traverse (Expression.traverse f) e
                <*> traverse (traverse (Expression.traverse f)) es
    | .fn qs e =>
        .fn <$> traverse (bitraverse f (traverse (Expression.traverse f))) qs
            <*> traverse (Expression.traverse f) e
    | .fnSet e₁ e₂ =>
        .fnSet <$> traverse (Expression.traverse f) e₁
               <*> traverse (Expression.traverse f) e₂
    | .record fs =>
        .record <$> traverse (Prod.traverse₃ (traverse f) pure (traverse (Expression.traverse f))) fs
    | .recordSet fs =>
        .recordSet <$> traverse (Prod.traverse₃ (traverse f) pure (traverse (Expression.traverse f))) fs
    | .except e upds =>
        .except <$> traverse (Expression.traverse f) e
                <*> traverse (bitraverse (traverse (bitraverse pure (traverse (traverse (Expression.traverse f))))) (traverse (Expression.traverse f))) upds
    | .recordAccess e v =>
        (.recordAccess · v) <$> traverse (Expression.traverse f) e
    | .tuple es =>
        .tuple <$> traverse (traverse (Expression.traverse f)) es
    | .if e₁ e₂ e₃ =>
        .if <$> traverse (Expression.traverse f) e₁
            <*> traverse (Expression.traverse f) e₂
            <*> traverse (Expression.traverse f) e₃
    | .case es e =>
        .case <$> traverse (bitraverse (traverse (Expression.traverse f)) (traverse (Expression.traverse f))) es
              <*> traverse (traverse (Expression.traverse f)) e
    | .conj es =>
        .conj <$> traverse (traverse (Expression.traverse f)) es
    | .disj es =>
        .disj <$> traverse (traverse (Expression.traverse f)) es
    | .stutter e₁ e₂ =>
        .stutter <$> traverse (Expression.traverse f) e₁
                 <*> traverse (Expression.traverse f) e₂

  instance : Traversable Expression where
    traverse := Expression.traverse

  instance instTraversableProd.{u} {α : Type u} : Traversable (Prod.{u, u} α) where
    traverse f x := ({x with snd := ·}) <$> f x.snd

  -- TODO: support distfix heads for operator definitions
  -- (keep in mind that to define the prefix `-`, one has to write `-. _ == _`, not `- _ == _`, somehow)

  inductive Declaration (α : Type) : Type
    | constants : List (Located 𝒱 × List α) → Declaration α
    | «variables» : List (Located 𝒱 × List α) → Declaration α
    | assume : Located (Expression α) → Declaration α
    /--
      An operator definition with optionally higher-order arguments.
      The `Nat` value associated to each parameter denotes its number of parameters (e.g. 0 for `x`, 3 for `F(_, _, _)`, …).
    -/
    | operator : List α → Located 𝒱 → List (Located 𝒱 × Nat) → Located (Expression α) → Declaration α
    /-- A function definition given a domain for all its arguments. -/
    | function : List α → Located 𝒱 → List (Located 𝒱 × Located (Expression α)) → Located (Expression α) → Declaration α
    deriving Repr, Functor, Traversable

  structure Module (α β : Type _) : Type _ where
    name : Located 𝒱
    «extends» : List (Located 𝒱)
    declarations₁ : List (Located (Declaration β))
    pcalAlgorithm : Option α -- (SurfacePlusCal.Algorithm Expr)
    declarations₂ : List (Located (Declaration β))
    deriving Repr

  instance : Bifunctor Module where
    bimap f g m := {m with
      declarations₁ := ((g <$> ·) <$> ·) <$> m.declarations₁
      pcalAlgorithm := f <$> m.pcalAlgorithm
      declarations₂ := ((g <$> ·) <$> ·) <$> m.declarations₂
    }

  instance : Bitraversable Module where
    bitraverse f g m :=
      ({m with declarations₁ := ·, pcalAlgorithm := ·, declarations₂ := ·})
        <$> traverse (traverse (traverse g)) m.declarations₁
        <*> traverse f m.pcalAlgorithm
        <*> traverse (traverse (traverse g)) m.declarations₂
end SurfaceTLAPlus
