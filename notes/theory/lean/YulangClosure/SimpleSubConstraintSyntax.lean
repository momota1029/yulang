import YulangClosure.Contracts

/-!
Forward constraint soundness for the structural native Simple-sub operations.

Source: `2026-10-13-intrusion-source-preservation-proof.md`, section 4's
one-sided extrusion argument; `2026-10-24-birth-level-scc-intrusion.md`;
native `term.rs`'s Function/Record/Tuple/Variant carriers. Function has the
four distinct ports (-,-,+,+), including both effect ports. Labels, optional
bits, tags, tuple order, row kinds and occurrence identities are retained.

This is an independent structural constraint derivation language, not a new
definition of source typing. Opaque atoms carry unchanged leaf identities;
contextual effect admission, complete Call meaning, recursive solution
existence, source generation/generalization and Rust correspondence are OPEN.
In particular, a terminal valuation is an input to forward reflection; this
module does not equate native successful return with existence of that input.
-/
namespace YulangClosure.SimpleSub

inductive Kind where
  | value | effect
  deriving DecidableEq, Repr

inductive Polarity where
  | positive | negative
  deriving DecidableEq, Repr

def Polarity.flip : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

inductive Term : Kind → Type where
  | var {k} (identity : Nat) : Term k
  | atom {k} (identity : Nat) : Term k
  | bottom {k} : Term k
  | top {k} : Term k
  | union {k} (left right : Term k) : Term k
  | intersection {k} (left right : Term k) : Term k
  | function (argument : Term .value) (argumentEffect resultEffect : Term .effect)
      (result : Term .value) : Term .value
  | recordNil : Term .value
  | recordCons (label : Nat) (optional : Bool) (field tail : Term .value) : Term .value
  | tupleNil : Term .value
  | tupleCons (head tail : Term .value) : Term .value
  | variantNil : Term .value
  | variantCons (tag : Nat) (payloads tail : Term .value) : Term .value
  deriving Repr

abbrev Valuation := (k : Kind) → Nat → Term k
abbrev Renaming := Kind → Nat → Nat

def Term.subst (ρ : Valuation) {k} : Term k → Term k
  | .var identity => ρ k identity
  | .atom identity => .atom identity
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (left.subst ρ) (right.subst ρ)
  | .intersection left right => .intersection (left.subst ρ) (right.subst ρ)
  | .function a ae re r => .function (a.subst ρ) (ae.subst ρ) (re.subst ρ) (r.subst ρ)
  | .recordNil => .recordNil
  | .recordCons label optional field tail =>
      .recordCons label optional (field.subst ρ) (tail.subst ρ)
  | .tupleNil => .tupleNil
  | .tupleCons head tail => .tupleCons (head.subst ρ) (tail.subst ρ)
  | .variantNil => .variantNil
  | .variantCons tag payloads tail => .variantCons tag (payloads.subst ρ) (tail.subst ρ)

def Term.rename (q : Renaming) {k} (t : Term k) : Term k :=
  t.subst (fun k identity => .var (q k identity))

theorem Term.subst_id {k} (t : Term k) : t.subst (fun _ identity => .var identity) = t := by
  induction t <;> simp_all [Term.subst]

theorem Term.subst_comp (ρ σ : Valuation) {k} (t : Term k) :
    (t.subst ρ).subst σ = t.subst (fun k identity => (ρ k identity).subst σ) := by
  induction t <;> simp_all [Term.subst]

theorem Term.rename_subst (q : Renaming) (ρ : Valuation) {k} (t : Term k) :
    (t.rename q).subst ρ = t.subst (fun k identity => ρ k (q k identity)) := by
  simp only [Term.rename, Term.subst_comp, Term.subst]

/-- Structural derivability, defined independently of extrusion and histories.
Record/variant rules here preserve the complete constructor shape. The rule
set does not purport to give complete optional-row or effect admission. -/
inductive Sub : {k : Kind} → Term k → Term k → Prop where
  | refl (t : Term k) : Sub t t
  | trans {a b c : Term k} : Sub a b → Sub b c → Sub a c
  | bottom (t : Term k) : Sub .bottom t
  | top (t : Term k) : Sub t .top
  | unionLeft (a b : Term k) : Sub a (.union a b)
  | unionRight (a b : Term k) : Sub b (.union a b)
  | unionElim {a b c : Term k} : Sub a c → Sub b c → Sub (.union a b) c
  | intersectionLeft (a b : Term k) : Sub (.intersection a b) a
  | intersectionRight (a b : Term k) : Sub (.intersection a b) b
  | intersectionIntro {a b c : Term k} : Sub c a → Sub c b → Sub c (.intersection a b)
  | unionMono {a a' b b' : Term k} :
      Sub a a' → Sub b b' → Sub (.union a b) (.union a' b')
  | intersectionMono {a a' b b' : Term k} :
      Sub a a' → Sub b b' → Sub (.intersection a b) (.intersection a' b')
  | function {a a' r r' : Term .value} {ae ae' re re' : Term .effect} :
      Sub a' a → Sub ae' ae → Sub re re' → Sub r r' →
      Sub (.function a ae re r) (.function a' ae' re' r')
  | recordCons {field field' tail tail' : Term .value} (label : Nat) (optional : Bool) :
      Sub field field' → Sub tail tail' →
      Sub (.recordCons label optional field tail) (.recordCons label optional field' tail')
  | tupleCons {head head' tail tail' : Term .value} :
      Sub head head' → Sub tail tail' → Sub (.tupleCons head tail) (.tupleCons head' tail')
  | variantCons {payloads payloads' tail tail' : Term .value} (tag : Nat) :
      Sub payloads payloads' → Sub tail tail' →
      Sub (.variantCons tag payloads tail) (.variantCons tag payloads' tail')

theorem Sub.subst (ρ : Valuation) {k} {a b : Term k} (h : Sub a b) :
    Sub (a.subst ρ) (b.subst ρ) := by
  induction h with
  | refl t => exact .refl _
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | bottom t => exact .bottom _
  | top t => exact .top _
  | unionLeft a b => exact .unionLeft _ _
  | unionRight a b => exact .unionRight _ _
  | unionElim _ _ ih₁ ih₂ => exact .unionElim ih₁ ih₂
  | intersectionLeft a b => exact .intersectionLeft _ _
  | intersectionRight a b => exact .intersectionRight _ _
  | intersectionIntro _ _ ih₁ ih₂ => exact .intersectionIntro ih₁ ih₂
  | unionMono _ _ ih₁ ih₂ => exact .unionMono ih₁ ih₂
  | intersectionMono _ _ ih₁ ih₂ => exact .intersectionMono ih₁ ih₂
  | function _ _ _ _ iha ihae ihre ihr => exact .function iha ihae ihre ihr
  | recordCons label optional _ _ ihf iht => exact .recordCons label optional ihf iht
  | tupleCons _ _ ihh iht => exact .tupleCons ihh iht
  | variantCons tag _ _ ihp iht => exact .variantCons tag ihp iht

structure Constraint where
  kind : Kind
  lower : Term kind
  upper : Term kind

def Constraint.Satisfied (ρ : Valuation) (c : Constraint) : Prop :=
  Sub (c.lower.subst ρ) (c.upper.subst ρ)

def Constraint.rename (q : Renaming) (c : Constraint) : Constraint :=
  ⟨c.kind, c.lower.rename q, c.upper.rename q⟩

abbrev Store := List Constraint

def Store.Satisfied (ρ : Valuation) (store : Store) : Prop :=
  ∀ c, c ∈ store → c.Satisfied ρ

@[simp] theorem Store.satisfied_nil (ρ : Valuation) : Store.Satisfied ρ [] := by
  intro c hc
  cases hc

@[simp] theorem Store.satisfied_cons (ρ : Valuation) (c : Constraint) (store : Store) :
    Store.Satisfied ρ (c :: store) ↔ c.Satisfied ρ ∧ Store.Satisfied ρ store := by
  simp only [Store.Satisfied, List.mem_cons, forall_eq_or_imp]

@[simp] theorem Store.satisfied_append (ρ : Valuation) (left right : Store) :
    Store.Satisfied ρ (left ++ right) ↔ Store.Satisfied ρ left ∧ Store.Satisfied ρ right := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨hl, hr⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hl c hc
    · exact hr c hc

theorem Store.subset (ρ : Valuation) {left right : Store}
    (included : ∀ c, c ∈ left → c ∈ right) (h : right.Satisfied ρ) : left.Satisfied ρ := by
  intro c hc
  exact h c (included c hc)

theorem Constraint.rename_satisfied (q : Renaming) (ρ : Valuation) (c : Constraint) :
    (c.rename q).Satisfied ρ ↔ c.Satisfied (fun k identity => ρ k (q k identity)) := by
  simp only [Constraint.rename, Constraint.Satisfied, Term.rename_subst]

/-- Every original clause is retained under canonicalization; a solution is
pulled back along the actual row map, preserving aliases and kind. -/
theorem Store.quotient_pullback (q : Renaming) (ρ : Valuation) (store : Store) :
    Store.Satisfied ρ (store.map (Constraint.rename q)) ↔
      store.Satisfied (fun k identity => ρ k (q k identity)) := by
  constructor
  · intro h c hc
    exact (Constraint.rename_satisfied q ρ c).mp (h _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
  · intro h c hc
    rcases List.mem_map.mp hc with ⟨original, horiginal, rfl⟩
    exact (Constraint.rename_satisfied q ρ original).mpr (h original horiginal)

end YulangClosure.SimpleSub
