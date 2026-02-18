import PlusCalCompiler.Position
import PlusCalCompiler.SurfaceTLAPlus.Syntax
import Extra.String
import Extra.Sum

/-! # Core TLA⁺ -/

namespace CoreTLAPlus
  export SurfaceTLAPlus (Typ)

  -- /--
  --   TLA⁺ types, in the [same format as Apalache](https://apalache-mc.org/docs/adr/002adr-types.html),
  --   except we don't support type aliases.
  -- -/
  -- protected inductive «Type».{u} : Type u
  --   /-- `Bool`, the type of values `TRUE` and `FALSE`. -/
  --   | bool
  --   /-- `Int`, the type of integer values. -/
  --   | int
  --   /-- `Str` -/
  --   | str
  --   /--
  --     The type of functions from `dom` to `ran`, denoted `dom -> ran`.
  --     Multi-dimensional functions are represented as functions from tuples.
  --   -/
  --   | function (dom ran : CoreTLAPlus.«Type»)
  --   /-- The type of homogeneous sets of values of type `τ`, denoted `Set(τ)`. -/
  --   | set (τ : CoreTLAPlus.«Type»)
  --   /-- The type of homogeneous sequences of values of type `τ`, denoted `Seq(τ)`. -/
  --   | seq (τ : CoreTLAPlus.«Type»)
  --   /-- The type of (heterogeneous) tuples, denoted `<<τ₁, …, τₙ>>`. -/
  --   | tuple (τs : List CoreTLAPlus.«Type»)
  --   /-- The type of operators denoted `(dom₁, …, domₙ) => ran`. -/
  --   | operator (dom : List CoreTLAPlus.«Type») (ran : CoreTLAPlus.«Type»)
  --   /-- Type variables, used to represent implicit universal type quantification. -/
  --   | var (name : String)
  --   /-- Constants, as in uninterpreted names (basically opaque types). -/
  --   | const (name : String)
  --   /-- A "named" tuple, i.e. a tuple whose indices are named. -/
  --   | record (fields : List (String × CoreTLAPlus.«Type»))
  --   ----------------------------------------
  --   -- PlusCal-specific types, maybe we'll move these elsewhere at one point.
  --   /-- Channels and FIFOs. -/
  --   -- NOTE: maybe we should have two different types for channels and FIFOs?
  --   | channel (τ : CoreTLAPlus.«Type»)
  --   /-- An abstract type for "addresses". -/
  --   | address

  inductive PrefixOperator.{u} : Type u
    /-- Logical negation. -/
    | «¬»
    | «-»
  with @[computed_field] prec : PrefixOperator → Nat
    | .«¬» => 4
    | .«-» => 12
  deriving BEq

  instance : DecidableEq PrefixOperator := by
    rintro (_|_) (_|_) <;> solve
      | apply isTrue; rfl
      | apply isFalse; nofun

  instance : ToString PrefixOperator where
    toString
      | .«¬» => "¬"
      | .«-» => "-"

  inductive InfixOperator.{u} : Type u
    /-- Value strict equality. -/
    | «=»
    /-- Set membership. -/
    | «∈»
    /-- Set union. -/
    | «∪»
    /-- Strictly bigger than. -/
    | «>»
    /-- Addition of numbers -/
    | «+»
    /-- Subtraction of numbers -/
    | «-»
  with @[computed_field] prec : InfixOperator → Nat
    | .«=» => 5
    | .«∈» => 5
    | .«∪» => 8
    | .«>» => 5
    | .«+» => 5
    | .«-» => 5
  deriving BEq

  instance : DecidableEq InfixOperator := by
    rintro (_|_) (_|_) <;> solve
      | apply isTrue; rfl
      | apply isFalse; nofun

  instance : ToString InfixOperator where
    toString
      | .«=» => "="
      | .«∈» => "∈"
      | .«∪» => "∪"
      | .«>» => ">"
      | .«+» => "+"
      | .«-» => "-"

  -- TODO: do we keep a deep embedding of TLA+?
  -- Or maybe we can try a shallow embedding (e.g. PHOAS-style or locally-nameless style)?

  inductive Expression.{u} (Typ : Type u) : Type u
    /-- An (unqualified) identifier. -/
    | var (name : String)
    /-- A string literal. -/
    | str (raw : String)
    /-- An integer literal. -/
    | nat (raw : String)
    /-- A boolean literal. -/
    | bool (raw : Bool)
    /-- A set literal `{e₁, …, eₙ}`. -/
    | set (elems : List (Expression Typ))
    /-- A record literal `[x₁ ↦ e₁, …, xₙ ↦ eₙ]`, with types ascribed to the fields. -/
    | record (fields : List (String × Typ × Expression Typ))
    /-- Prefix operator call `⊙ e`. -/
    | prefix (op : PrefixOperator) (e : Expression Typ)
    /-- Infix operator call `e₁ ⊙ e₂`. -/
    | infix (e₁ : Expression Typ) (op : InfixOperator) (e₂ : Expression Typ)
    /-- Function call `f[e₁, …, eₙ]`. -/
    | funcall (fn : Expression Typ) (args : List (Expression Typ))
    /-- Record access `e.x`. -/
    | access (e : Expression Typ) (x : String)
    /-- A literal sequence `Seq(⟨e₁, …, eₙ⟩)`. -/
    | seq (es : List (Expression Typ))
    /-- Operator call `f(e₁, …, eₙ)`. -/
    | opcall (fn : Expression Typ) (args : List (Expression Typ))
    /-- Function update `[x EXCEPT ![e₁, …, eₙ] = e]`. -/
    | except (e : Expression Typ) (upds : List ((List (List (Expression Typ) ⊕ String)) × Expression Typ))
    deriving Inhabited, BEq

  -- TODO: remove that partial
  partial instance Expression.hasDecEq.{u} {Typ : Type u} [DecidableEq Typ] : DecidableEq (Expression.{u} Typ) :=
    let rec go (e₁ e₂ : Expression Typ) : Decidable (e₁ = e₂) := match e₁, e₂ with
      -- Decide equality here
      | .var raw, .var raw' | .str raw, .str raw' | .nat raw, .nat raw' | .bool raw, .bool raw' =>
        if h : raw = raw' then isTrue (by rw [h])
        else isFalse λ h' ↦ by injections; absurd h; trivial
      | .set es, .set es' | .seq es, .seq es' =>
        match @List.hasDecEq _ go es es' with
        | .isTrue h₂ => isTrue (by rw [h₂])
        | .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
      | .record fields, .record fields' =>
        match @List.hasDecEq _ (@Prod.hasDecEq _ _ inferInstance (@Prod.hasDecEq _ _ inferInstance go)) fields fields' with
        | .isTrue h₂ => isTrue (by rw [h₂])
        | .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
      | .prefix op e, .prefix op' e' =>
        if h₁ : op = op' then
          match go e e' with
          | .isTrue h₂ => isTrue (by rw [h₁, h₂])
          | .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
        else
          isFalse λ h' ↦ by injections; absurd h₁; trivial
      | .infix e₁ op e₂, .infix e₁' op' e₂' =>
        if h₁ : op = op' then
          match go e₁ e₁', go e₂ e₂' with
          | .isTrue h₂, .isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
          | .isTrue h₂, .isFalse h₃ => isFalse λ h' ↦ by injections; contradiction
          | .isFalse h₂, .isTrue h₃ => isFalse λ h' ↦ by injections; contradiction
          | .isFalse h₂, .isFalse h₃ => isFalse λ h' ↦ by injections; contradiction
        else
          isFalse λ h' ↦ by injections; absurd h₁; trivial
      | .funcall fn args, .funcall fn' args' | .opcall fn args, .opcall fn' args' =>
        match go fn fn', @List.hasDecEq _ go args args' with
        | .isTrue h₂, .isTrue h₃ => isTrue (by rw [h₂, h₃])
        | .isTrue h₂, .isFalse h₃ => isFalse λ h' ↦ by injections; contradiction
        | .isFalse h₂, .isTrue h₃ => isFalse λ h' ↦ by injections; contradiction
        | .isFalse h₂, .isFalse h₃ => isFalse λ h' ↦ by injections; contradiction
      | .access e x, .access e' x' =>
        if h₁ : x = x' then
          match go e e' with
          | .isTrue h₂ => isTrue (by rw [h₁, h₂])
          | .isFalse h₂ => isFalse λ h' ↦ by injections; contradiction
        else
          isFalse λ h' ↦ by injections; absurd h₁; trivial
      | .except e upds, .except e' upds' =>
        match go e e', @List.hasDecEq _ (@Prod.hasDecEq _ _ (@List.hasDecEq _ (@Sum.hasDecEq _ _ (@List.hasDecEq _ go) inferInstance)) go) upds upds' with
        | .isTrue h₂, .isTrue h₃ => isTrue (by rw [h₂, h₃])
        | .isTrue h₂, .isFalse h₃ => isFalse λ _ ↦ by injections; contradiction
        | .isFalse h₂, .isTrue h₃ => isFalse λ _ ↦ by injections; contradiction
        | .isFalse h₂, .isFalse h₃ => isFalse λ _ ↦ by injections; contradiction
      -- Other trivial cases that all need to be written
      | .var .., .str .. | .var .., .nat .. | .var .., .bool .. | .var .., .set .. | .var .., .record ..
      | .var .., .prefix .. | .var .., .infix .. | .var .., .funcall .. | .var .., .access .. | .var .., .seq ..
      | .var .., .opcall .. | .var .., .except .. => isFalse nofun
      | .str .., .var .. | .str .., .nat .. | .str .., .bool .. | .str .., .set .. | .str .., .record ..
      | .str .., .prefix .. | .str .., .infix .. | .str .., .funcall .. | .str .., .access .. | .str .., .seq ..
      | .str .., .opcall .. | .str .., .except .. => isFalse nofun
      | .nat .., .var .. | .nat .., .str .. | .nat .., .bool .. | .nat .., .set .. | .nat .., .record ..
      | .nat .., .prefix .. | .nat .., .infix .. | .nat .., .funcall .. | .nat .., .access .. | .nat .., .seq ..
      | .nat .., .opcall .. | .nat .., .except .. => isFalse nofun
      | .bool .., .var .. | .bool .., .str .. | .bool .., .nat .. | .bool .., .set .. | .bool .., .record ..
      | .bool .., .prefix .. | .bool .., .infix .. | .bool .., .funcall .. | .bool .., .access .. | .bool .., .seq ..
      | .bool .., .opcall .. | .bool .., .except .. => isFalse nofun
      | .set .., .var .. | .set .., .str .. | .set .., .nat .. | .set .., .bool .. | .set .., .record ..
      | .set .., .prefix .. | .set .., .infix .. | .set .., .funcall .. | .set .., .access .. | .set .., .seq ..
      | .set .., .opcall .. | .set .., .except .. => isFalse nofun
      | .record .., .var .. | .record .., .str .. | .record .., .nat .. | .record .., .bool .. | .record .., .set ..
      | .record .., .prefix .. | .record .., .infix .. | .record .., .funcall .. | .record .., .access .. | .record .., .seq ..
      | .record .., .opcall .. | .record .., .except .. => isFalse nofun
      | .prefix .., .var .. | .prefix .., .str .. | .prefix .., .nat .. | .prefix .., .bool .. | .prefix .., .set ..
      | .prefix .., .record .. | .prefix .., .infix .. | .prefix .., .funcall .. | .prefix .., .access .. | .prefix .., .seq ..
      | .prefix .., .opcall .. | .prefix .., .except .. => isFalse nofun
      | .infix .., .var .. | .infix .., .str .. | .infix .., .nat .. | .infix .., .bool .. | .infix .., .set ..
      | .infix .., .record .. | .infix .., .prefix .. | .infix .., .funcall .. | .infix .., .access .. | .infix .., .seq ..
      | .infix .., .opcall .. | .infix .., .except .. => isFalse nofun
      | .funcall .., .var .. | .funcall .., .str .. | .funcall .., .nat .. | .funcall .., .bool .. | .funcall .., .set ..
      | .funcall .., .record .. | .funcall .., .prefix .. | .funcall .., .infix .. | .funcall .., .access .. | .funcall .., .seq ..
      | .funcall .., .opcall .. | .funcall .., .except .. => isFalse nofun
      | .access .., .var .. | .access .., .str .. | .access .., .nat .. | .access .., .bool .. | .access .., .set ..
      | .access .., .record .. | .access .., .prefix .. | .access .., .infix .. | .access .., .funcall .. | .access .., .seq ..
      | .access .., .opcall .. | .access .., .except .. => isFalse nofun
      | .seq .., .var .. | .seq .., .str .. | .seq .., .nat .. | .seq .., .bool .. | .seq .., .set ..
      | .seq .., .record .. | .seq .., .prefix .. | .seq .., .infix .. | .seq .., .funcall .. | .seq .., .access ..
      | .seq .., .opcall .. | .seq .., .except .. => isFalse nofun
      | .opcall .., .var .. | .opcall .., .str .. | .opcall .., .nat .. | .opcall .., .bool .. | .opcall .., .set ..
      | .opcall .., .record .. | .opcall .., .prefix .. | .opcall .., .infix .. | .opcall .., .funcall .. | .opcall .., .seq ..
      | .opcall .., .access .. | .opcall .., .except .. => isFalse nofun
      | .except .., .var .. | .except .., .str .. | .except .., .nat .. | .except .., .bool .. | .except .., .set ..
      | .except .., .record .. | .except .., .prefix .. | .except .., .infix .. | .except .., .funcall .. | .except .., .seq ..
      | .except .., .access .. | .except .., .opcall .. => isFalse nofun
    go

  def Expression.freeVars.{u} {Typ : Type u} : Expression Typ → List String
    | .var name => [name]
    | .str _ => []
    | .nat _ => []
    | .bool _ => []
    | .set elems => elems.attach.flatMap λ ⟨e, _⟩ => e.freeVars
    | .record fields => fields.attach.flatMap λ ⟨⟨_n, _τ, e⟩, _⟩ ↦ e.freeVars
    | .prefix _ e => e.freeVars
    | .infix e₁ _ e₂ => e₁.freeVars ∪ e₂.freeVars
    | .funcall fn args => fn.freeVars ∪ (args.attach.flatMap λ ⟨e, _⟩ ↦ e.freeVars)
    | .access e _ => e.freeVars
    | .seq es => es.attach.flatMap λ ⟨e, _⟩ => e.freeVars
    | .opcall fn args => fn.freeVars ∪ (args.attach.flatMap λ ⟨e, _⟩ ↦ e.freeVars)
    | .except fn upds => fn.freeVars ∪ upds.attach.flatMap λ ⟨⟨upds', e⟩, _⟩ ↦ upds'.attach.flatMap (λ | ⟨.inl es, _⟩ => es.attach.flatMap (λ ⟨e', _⟩ ↦ e'.freeVars) | ⟨.inr _, _⟩ => ∅) ∪ e.freeVars
  termination_by e => e
  decreasing_by
    all_goals simp_wf; try decreasing_trivial
    · trans sizeOf (_n, _τ, e) <;> decreasing_trivial
    · calc
        sizeOf es ≤ sizeOf (Sum.inl (β := String) es) := by decreasing_trivial
        _ ≤ sizeOf upds' := by apply Nat.le_of_lt; decreasing_trivial
        _ ≤ sizeOf (upds', e) := by decreasing_trivial
        _ ≤ sizeOf upds := by apply Nat.le_of_lt; decreasing_trivial
        _ ≤ _ := by decreasing_trivial
    · calc
        sizeOf e < sizeOf (upds', e) := by decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial

  def Expression.replace (e : Expression Typ) (v : String) (e' : Expression Typ) : Expression Typ := match_source e with
    | .var name, pos => if v = name then e' else .var name @@ pos
    | .str raw, pos => .str raw @@ pos
    | .nat raw, pos => .nat raw @@ pos
    | .bool raw, pos => .bool raw @@ pos
    | .set elems, pos => .set (elems.attach.map λ ⟨e, _⟩ => e.replace v e') @@ pos
    | .record fields, pos => .record (fields.attach.map λ ⟨⟨x, τ, e⟩, _⟩ ↦ ⟨x, τ, e.replace v e'⟩) @@ pos
    | .prefix op e, pos => .prefix op (e.replace v e') @@ pos
    | .infix e₁ op e₂, pos => .infix (e₁.replace v e') op (e₂.replace v e') @@ pos
    | .funcall fn args, pos => .funcall (fn.replace v e') (args.attach.map λ ⟨e, _⟩ ↦ e.replace v e') @@ pos
    | .access e x, pos => .access (e.replace v e') x @@ pos
    | .seq es, pos => .seq (es.attach.map λ ⟨e, _⟩ ↦ e.replace v e') @@ pos
    | .opcall fn args, pos => .opcall (fn.replace v e') (args.attach.map λ ⟨e, _⟩ ↦ e.replace v e') @@ pos
    | .except fn upds, pos => .except (fn.replace v e') (upds.attach.map λ ⟨⟨upds', e⟩, _⟩ ↦ ⟨upds'.attach.map λ | ⟨.inl es, _⟩ => .inl (es.attach.map λ ⟨e'', _⟩ ↦ e''.replace v e') | ⟨.inr x, _⟩ => .inr x, e.replace v e'⟩) @@ pos
  termination_by e
  decreasing_by
    all_goals simp_wf; try decreasing_trivial
    · trans sizeOf (x, τ, e) <;> decreasing_trivial
    · calc
        sizeOf es ≤ sizeOf (Sum.inl (β := String) es) := by decreasing_trivial
        _ ≤ sizeOf upds' := by apply Nat.le_of_lt; decreasing_trivial
        _ ≤ sizeOf (upds', e) := by decreasing_trivial
        _ ≤ sizeOf upds := by apply Nat.le_of_lt; decreasing_trivial
        _ ≤ _ := by decreasing_trivial
    · calc
        sizeOf e < sizeOf (upds', e) := by decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial

  partial instance {Typ : Type _} : ToString (Expression Typ) where
    toString :=
      let rec go : Expression Typ → String
        | .var name => name
        | .str raw => s!"{raw.escape}"
        | .nat raw => s!"{raw}"
        | .bool raw => s!"{raw}"
        | .set elems => "{" ++ String.intercalate ", " (elems.map go) ++ "}"
        | .record fields => "[" ++ String.intercalate ", " (fields.map λ ⟨v, _, e⟩ ↦ v ++ " |-> " ++ go e) ++ "]"
        | .prefix op e => s!"{op} {go e}"
        | .infix e₁ op e₂ => s!"({go e₁}) {op} ({go e₂})"
        | .funcall fn args => s!"({go fn})[{String.intercalate ", " (args.map go)}]"
        | .opcall fn args => s!"({go fn})({String.intercalate ", " (args.map go)})"
        | .access e x => s!"({go e}).{x}"
        | .seq es => s!"Seq(<<{String.intercalate ", " (es.map go)}>>)"
        | .except e upds => s!"[{go e} EXCEPT {String.intercalate ", " (upds.map λ | ⟨upds, e⟩ => s!"!{String.join (upds.map λ | .inl es => s!"[{String.intercalate ", " (es.map go)}]" | .inr x => s!".{x}")} = {go e}")}]"
      go
