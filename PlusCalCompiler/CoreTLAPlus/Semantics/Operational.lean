import PlusCalCompiler.CoreTLAPlus.Syntax
import Mathlib.Data.List.AList
import Extra.Prod

namespace CoreTLAPlus
  /-- Expressions in Weak Head Normal Form (WHNF). -/
  inductive Value.{u} : Type u
    | int (raw : Int)
    | str (raw : String)
    | bool (raw : Bool)
    | set (vs : List Value)
    | seq (vs : List Value)
    | record (fs : List (String × Value))
    | tuple (vs : List Value)
    | lam (x : String) (body : Expression.{u} Typ)
    | fn (vs : List (Value × Value))
    | prim (name : String)
    deriving BEq

  mutual
    private def Value.hasDecEq.aux₁.{u} : DecidableEq (List Value.{u})
      | [], [] => .isTrue rfl
      | [], _ :: _ => .isFalse nofun
      | _ :: _, [] => .isFalse nofun
      | v :: vs, v' :: vs' => match Value.hasDecEq v v', Value.hasDecEq.aux₁ vs vs' with
        | .isTrue h₁, .isTrue h₂ => .isTrue (by rw [h₁, h₂])
        | .isTrue h₁, .isFalse h₂ => .isFalse λ h₃ ↦ by injections; contradiction
        | .isFalse h₁, .isTrue h₂ => .isFalse λ h₃ ↦ by injections; contradiction
        | .isFalse h₁, .isFalse h₂ => .isFalse λ h₃ ↦ by injections; contradiction

    private def Value.hasDecEq.aux₂.{u} : DecidableEq (List (Value.{u} × Value.{u}))
      | [], [] => .isTrue rfl
      | [], _ :: _ => .isFalse nofun
      | _ :: _, [] => .isFalse nofun
      | ⟨v₁, v₂⟩ :: vs, ⟨v₁', v₂'⟩ :: vs' => match Value.hasDecEq v₁ v₁', Value.hasDecEq v₂ v₂', Value.hasDecEq.aux₂ vs vs' with
        | .isTrue h₁, .isTrue h₂, .isTrue h₃ => .isTrue (by rw [h₁, h₂, h₃])
        | .isTrue h₁, .isFalse h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isTrue h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isTrue h₂, .isTrue h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isTrue h₁, .isTrue h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isTrue h₁, .isFalse h₂, .isTrue h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isFalse h₂, .isTrue h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isFalse h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction

    private def Value.hasDecEq.aux₃.{u} : DecidableEq (List (String × Value.{u}))
      | [], [] => .isTrue rfl
      | [], _ :: _ => .isFalse nofun
      | _ :: _, [] => .isFalse nofun
      | ⟨v₁, v₂⟩ :: vs, ⟨v₁', v₂'⟩ :: vs' => match inferInstanceAs (Decidable (v₁ = v₁')), Value.hasDecEq v₂ v₂', Value.hasDecEq.aux₃ vs vs' with
        | .isTrue h₁, .isTrue h₂, .isTrue h₃ => .isTrue (by rw [h₁, h₂, h₃])
        | .isTrue h₁, .isFalse h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isTrue h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isTrue h₂, .isTrue h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isTrue h₁, .isTrue h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isTrue h₁, .isFalse h₂, .isTrue h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isFalse h₂, .isTrue h₃ => .isFalse λ h₄ ↦ by injections; contradiction
        | .isFalse h₁, .isFalse h₂, .isFalse h₃ => .isFalse λ h₄ ↦ by injections; contradiction

    protected def Value.hasDecEq.{u} : DecidableEq Value.{u}
      | .int raw, .int raw' | .str raw, .str raw' | .bool raw, .bool raw' | .prim raw, .prim raw' =>
        if h : raw = raw' then
          isTrue (by rw [h])
        else
          isFalse λ h' ↦ by injections; absurd h; trivial
      | .set vs, .set vs' | .seq vs, .seq vs' | .tuple vs, .tuple vs' =>
        match Value.hasDecEq.aux₁ vs vs' with
        | .isTrue h => .isTrue (by rw [h])
        | .isFalse h => .isFalse λ h' ↦ by injections; contradiction
      | .record fs, .record fs' =>
        match Value.hasDecEq.aux₃ fs fs' with
        | .isTrue h => isTrue (by rw [h])
        | .isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      | .lam x body, .lam x' body' =>
        if h : x = x' ∧ body = body' then
          isTrue (by rw [h.left, h.right])
        else
          isFalse λ h' ↦ by injections; absurd h; trivial
      | .fn vs, .fn vs' =>
        match Value.hasDecEq.aux₂ vs vs' with
        | .isTrue h => isTrue (by rw [h])
        | .isFalse h => isFalse λ h' ↦ by injections; absurd h; trivial
      -- Trivial cases where no decision is needed
      | .int .., .str .. | .int .., .bool .. | .int .., .set .. | .int .., .seq .. | .int .., .record ..
      | .int .., .tuple .. | .int .., .lam .. | .int .., .fn .. | .int .., .prim .. => isFalse nofun
      | .str .., .int .. | .str .., .bool .. | .str .., .set .. | .str .., .seq .. | .str .., .record ..
      | .str .., .tuple .. | .str .., .lam .. | .str .., .fn .. | .str .., .prim .. => isFalse nofun
      | .bool .., .int .. | .bool .., .str .. | .bool .., .set .. | .bool .., .seq .. | .bool .., .record ..
      | .bool .., .tuple .. | .bool .., .lam .. | .bool .., .fn .. | .bool .., .prim .. => isFalse nofun
      | .set .., .int .. | .set .., .str .. | .set .., .bool .. | .set .., .seq .. | .set .., .record ..
      | .set .., .tuple .. | .set .., .lam .. | .set .., .fn .. | .set .., .prim .. => isFalse nofun
      | .seq .., .int .. | .seq .., .str .. | .seq .., .bool .. | .seq .., .set .. | .seq .., .record ..
      | .seq .., .tuple .. | .seq .., .lam .. | .seq .., .fn .. | .seq .., .prim .. => isFalse nofun
      | .record .., .int .. | .record .., .str .. | .record .., .bool .. | .record .., .set .. | .record .., .seq ..
      | .record .., .tuple .. | .record .., .lam .. | .record .., .fn .. | .record .., .prim .. => isFalse nofun
      | .tuple .., .int .. | .tuple .., .str .. | .tuple .., .bool .. | .tuple .., .set .. | .tuple .., .seq ..
      | .tuple .., .record .. | .tuple .., .lam .. | .tuple .., .fn .. | .tuple .., .prim .. => isFalse nofun
      | .lam .., .int .. | .lam .., .str .. | .lam .., .bool .. | .lam .., .set .. | .lam .., .seq ..
      | .lam .., .record .. | .lam .., .tuple .. | .lam .., .fn .. | .lam .., .prim .. => isFalse nofun
      | .fn .., .int .. | .fn .., .str .. | .fn .., .bool .. | .fn .., .set .. | .fn .., .seq ..
      | .fn .., .record .. | .fn .., .tuple .. | .fn .., .lam .. | .fn .., .prim .. => isFalse nofun
      | .prim .., .int .. | .prim .., .str .. | .prim .., .bool .. | .prim .., .set .. | .prim .., .seq ..
      | .prim .., .record .. | .prim .., .tuple .. | .prim .., .lam .. | .prim .., .fn .. => isFalse nofun
  end

  instance : DecidableEq Value := Value.hasDecEq

  abbrev Memory.{u} : Type u := AList λ _ : String ↦ Value.{u}

  def Head (args : List Value) : Option Value := do
    if h : args.length = 1 then
      let .seq vs := args[0] | throw ()
      vs[0]?
    else
      throw ()

  def Tail (args : List Value) : Option Value := do
    if h : args.length = 1 then
      let .seq (v :: vs) := args[0] | throw ()
      pure (.seq vs)
    else
      throw ()

  def Len (args : List Value) : Option Value := do
    if h : args.length = 1 then
      let .seq vs := args[0] | throw ()
      pure (.int <| vs.length)
    else
      throw ()

  def prims.{u} : AList λ _ : String ↦ List Value.{u} → Option Value.{u} :=
    AList.insert "Head" Head <|
    AList.insert "Tail" Tail <|
    AList.insert "Len" Len <|
    ∅

  def primFromName : (k : String) → k ∈ prims → Option Value
    | "Head", _ => pure (.prim "Head")
    | "Tail", _ => pure (.prim "Tail")
    | "Len", _ => pure (.prim "Len")
    | _, _ => throw ()

  local instance {α} [DecidableEq α] (a : α) (as : List α) : Decidable (a ∈ as) := List.instDecidableMemOfLawfulBEq a as

  def eval.{u} (M : Memory.{u}) : Expression Typ → Option Value.{u}
    | .var name => if h : name ∈ prims.{u} then primFromName name h else M.lookup name
    | .str raw => return .str raw
    | .nat raw => return .int (String.toInt! raw)
    | .bool raw => return .bool raw
    | .set elems => .set <$> elems.attach.traverse λ ⟨e, _⟩ ↦ eval M e
    | .record fields => .record <$> fields.attach.traverse λ ⟨⟨n, _τ, e⟩, _⟩ ↦ (n, ·) <$> eval M e
    | .prefix op e => do
      let e ← eval M e
      match op with
      | .«-» => match e with
        | .int n => return .int (-n)
        | _ => throw ()
      | .«¬» => match e with
        | .bool b => return .bool !b
        | _ => throw ()
    | .infix e₁ op e₂ => do
      let e₁ ← eval M e₁
      let e₂ ← eval M e₂
      match op with
      | .«+» => match e₁, e₂ with
        | .int n₁, .int n₂ => return .int (n₁ + n₂)
        | _, _ => throw ()
      | .«-» => match e₁, e₂ with
        | .int n₁, .int n₂ => return .int (n₁ - n₂)
        | _, _ => throw ()
      | .«>» => match e₁, e₂ with
        | .int n₁, .int n₂ => return .bool (n₁ > n₂)
        | _, _ => throw ()
      | .«∪» => match e₁, e₂ with
        | .set vs₁, .set vs₂ => return .set (vs₁ ∪ vs₂)
        | _, _ => throw ()
      | .«∈» => match e₁, e₂ with
        | v₁, .set vs₂ => return .bool (decide (v₁ ∈ vs₂))
        | _, _ => throw ()
      | .«=» => match e₁, e₂ with
        | .set _, .set _ | .str _, .str _ | .int _, .int _ | .bool _, .bool _ | .record _, .record _ | .prim _, .prim _
        | .seq _, .seq _ | .tuple _, .tuple _ =>
          -- can we compare functions?
          return .bool (decide (e₁ = e₂))
        | _, _ => throw ()
    | .funcall fn args => do
      let args ← args.attach.traverse λ ⟨e, _⟩ ↦ eval M e
      let .fn fn ← eval M fn | throw ()
      let tup : Value := if let [arg] := args then arg else Value.tuple args
      let ⟨_, v⟩ ← fn.find? λ ⟨k, _⟩ ↦ k == tup
      return v
    | .access e x => do
      let .record bs ← eval M e | throw ()
      bs.lookup x
    | .seq es => .seq <$> es.attach.traverse λ ⟨e, _⟩ ↦ eval M e
    | .opcall fn args => do
      let args ← args.attach.traverse λ ⟨e, _⟩ ↦ eval M e
      match ← eval M fn with
      | .prim op => (· <| args) =<< prims.lookup op
      | _ => throw ()
    | .except fn upds => do
      let fn ← eval M fn
      let upds : List (List (List Value ⊕ String) × Value.{u}) ← upds.attach.traverse λ ⟨⟨upd, e⟩, _⟩ ↦ do
        let upd ← upd.attach.traverse λ | ⟨.inr x, _⟩ => pure (.inr x)
                                        | ⟨.inl es, _⟩ => .inl <$> es.attach.traverse λ ⟨e', _⟩ ↦ eval M e'
        let e ← eval M e
        return ⟨upd, e⟩

      let rec doUpdate : Value → List (List Value ⊕ String) → Value → Option Value
        | _, [], v => return v
        | fn@(.record fs), .inr x :: vss, v => do
          -- Do something only if `x` is a field of the record
          if let .some ⟨_, v'⟩ := fs.find? λ ⟨y, _⟩ ↦ y == x then
            let v' ← doUpdate v' vss v
            return .record (fs.replaceF λ ⟨y, _⟩ ↦ if y == x then .some ⟨y, v'⟩ else .none)
          else
            return fn
        | fn@(.fn maps), .inl vs :: vss, v => do
          let tup := if let [v] := vs then v else Value.tuple vs
          if let .some ⟨_, v'⟩ := maps.find? λ ⟨k, _⟩ ↦ k == tup then
            let v ← doUpdate v' vss v
            return .fn (maps.replaceF λ ⟨y, _⟩ ↦ if y == tup then .some ⟨tup, v⟩ else .none)
          else
            return fn
        | _, _, _ => throw ()

      upds.foldlM (λ fn ⟨upds, e⟩ ↦ doUpdate fn upds e) fn
  termination_by e => e
  decreasing_by
    all_goals simp_wf; try decreasing_trivial
    · trans sizeOf (n, _τ, e) <;> decreasing_trivial
    · apply Nat.le_of_lt
      calc
        _ < sizeOf (Sum.inl (β := String) es) := by decreasing_trivial
        _ < sizeOf upd := by decreasing_trivial
        _ < sizeOf (upd, e) := by decreasing_trivial
        _ < _ := by decreasing_trivial
    · calc
        _ < sizeOf (upd, e) := by decreasing_trivial
        _ < sizeOf upds := by decreasing_trivial
        _ < _ := by decreasing_trivial

  notation:60 M:60 " ⊢ " e:0 " ⇒ " v:60 => eval M e = Option.some v
  notation:60 M:60 " ⊢ " e:0 " ↯" => eval M e = Option.none
