import Yulang.ProducerCanonicalBase

/-!
# Complete finite codes for open scalar-lattice expressions

Free type parameters keep shared identities and may be instantiated by any
finite contextual producer, including records, functions and both effect
rows. The source expressions normalized here use parameters, bases, `never`,
`any`, union and intersection. Their complete code quantifies over parameters
by a finite Boolean profile table; no residual semantic constraint is stored
in that code.

This finite test reduction is a theorem about this expression fragment only.
It does not replace the arbitrary-type environment in contextual demands.
The separating environments use actual arbitrary-type parameter instances;
the reverse proof still covers every instance and every contextual demand.
-/

namespace Yulang.ProducerCanonicalOpen

open Inference (Base)
open ProducerContextual

universe u
variable {n : Nat} {Row : Type u}

inductive Atom (n : Nat) where
  | var : Fin n → Atom n
  | base : Base → Atom n
  deriving DecidableEq, Repr

inductive Expr (n : Nat) where
  | atom : Atom n → Expr n
  | bottom : Expr n
  | top : Expr n
  | union : Expr n → Expr n → Expr n
  | inter : Expr n → Expr n → Expr n
  deriving DecidableEq, Repr

def atoms (n : Nat) : List (Atom n) :=
  (List.finRange n).map Atom.var ++ ProducerCanonicalBase.baseOrder.map Atom.base

@[simp] theorem mem_atoms (atom : Atom n) : atom ∈ atoms n := by
  cases atom <;> simp [atoms]

/-- Executable enumeration of all ordered sublists, including the empty one. -/
def sublists {α : Type} : List α → List (List α)
  | [] => [[]]
  | first :: rest => sublists rest ++ (sublists rest).map (first :: ·)

theorem mem_sublists_iff {α : Type} (part whole : List α) :
    part ∈ sublists whole ↔ List.Sublist part whole := by
  induction whole generalizing part with
  | nil => simp [sublists]
  | cons first rest ih =>
      simp only [sublists, List.mem_append, List.mem_map, ih, List.sublist_cons_iff]
      constructor
      · rintro (left | ⟨tail, member, rfl⟩)
        · exact Or.inl left
        · exact Or.inr ⟨tail, rfl, member⟩
      · rintro (left | ⟨tail, rfl, member⟩)
        · exact Or.inl left
        · exact Or.inr ⟨tail, member, rfl⟩

def profiles (n : Nat) : List (List (Atom n)) := sublists (atoms n)

@[simp] theorem mem_profiles (profile : List (Atom n)) :
    profile ∈ profiles n ↔ List.Sublist profile (atoms n) := mem_sublists_iff profile (atoms n)

def Atom.embed (parameters : Fin n → StructuralBase.Ty Row) : Atom n → StructuralBase.Ty Row
  | .var index => parameters index
  | .base scalar => .base scalar

def Expr.embed (parameters : Fin n → StructuralBase.Ty Row) : Expr n → StructuralBase.Ty Row
  | .atom entry => entry.embed parameters
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (first.embed parameters) (last.embed parameters)
  | .inter first last => .inter (first.embed parameters) (last.embed parameters)

def Expr.toTerm : Expr n → Inference.TyTerm (Fin n)
  | .atom (.var index) => .var index
  | .atom (.base scalar) => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union first.toTerm last.toTerm
  | .inter first last => .inter first.toTerm last.toTerm

/-- The embedding is the evaluation of the actual inference type-term syntax.
Every repeated parameter index refers to the same computation slot. -/
theorem toTerm_eval (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (parameters : Fin n → StructuralBase.Ty Row) (rows : Fin n → Row) (expression : Expr n) :
    expression.toTerm.eval (model Row empty join leRow) (fun index => (parameters index, rows index)) =
      expression.embed parameters := by
  induction expression with
  | atom atom => cases atom <;> rfl
  | bottom | top => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      simp only [Expr.toTerm, Inference.TyTerm.eval, Expr.embed]
      rw [ihf, ihl]
      rfl

def Expr.eval (profile : List (Atom n)) : Expr n → Bool
  | .atom entry => decide (entry ∈ profile)
  | .bottom => true
  | .top => false
  | .union first last => first.eval profile && last.eval profile
  | .inter first last => first.eval profile || last.eval profile

def Equivalent (leRow : Row → Row → Prop) (first last : Expr n) : Prop :=
  ∀ parameters : Fin n → StructuralBase.Ty Row,
    ProducerEq leRow (first.embed parameters) (last.embed parameters)

private def roleEnvironment (Row : Type u) (profile : List (Atom n)) : Environment Row :=
  ⟨fun _ => .bottom,
    fun _ => (ProducerCanonicalBase.baseOrder.filter (fun scalar => decide (Atom.base scalar ∈ profile))).map Head.base⟩

private def roleParameters (Row : Type u) (profile : List (Atom n)) : Fin n → StructuralBase.Ty Row :=
  fun index => if Atom.var index ∈ profile then .bottom else .top

private theorem atom_role_exact (leRow : Row → Row → Prop) (rank : Nat)
    (profile : List (Atom n)) (atom : Atom n) :
    ProbeAt leRow rank (roleEnvironment Row profile) (atom.embed (roleParameters Row profile)) (.role 0) ↔
      atom ∈ profile := by
  cases atom with
  | var index =>
      by_cases member : Atom.var index ∈ profile <;>
        cases rank <;> simp [Atom.embed, roleParameters, member, ProbeAt, ProbeStep]
  | base scalar =>
      cases rank <;> simp [Atom.embed, ProbeAt, ProbeStep, roleEnvironment]

theorem eval_role_exact (leRow : Row → Row → Prop) (rank : Nat)
    (profile : List (Atom n)) (expression : Expr n) :
    ProbeAt leRow rank (roleEnvironment Row profile)
      (expression.embed (roleParameters Row profile)) (.role 0) ↔ expression.eval profile = true := by
  induction expression with
  | atom atom => simp [Expr.embed, Expr.eval, atom_role_exact]
  | bottom => simp [Expr.embed, Expr.eval]
  | top => cases rank <;> simp [ProbeAt, ProbeStep, Expr.embed, Expr.eval]
  | union first last ihf ihl => simp [Expr.embed, Expr.eval, ihf, ihl]
  | inter first last ihf ihl => simp [Expr.embed, Expr.eval, ihf, ihl]

private theorem probe_embed_exact (leRow : Row → Row → Prop) (rank : Nat)
    (env : Environment Row) (observation : Observation Row) (nontrivial : observation ≠ .trivial)
    (parameters : Fin n → StructuralBase.Ty Row) (profile : List (Atom n))
    (atomsExact : ∀ atom, ProbeAt leRow rank env (atom.embed parameters) observation ↔ atom ∈ profile)
    (expression : Expr n) :
    ProbeAt leRow rank env (expression.embed parameters) observation ↔ expression.eval profile = true := by
  induction expression with
  | atom atom => simp [Expr.embed, Expr.eval, atomsExact]
  | bottom => simp [Expr.embed, Expr.eval]
  | top => cases rank <;> cases observation <;> simp_all [ProbeAt, ProbeStep, Expr.embed, Expr.eval]
  | union first last ihf ihl => simp [Expr.embed, Expr.eval, ihf, ihl]
  | inter first last ihf ihl => simp [Expr.embed, Expr.eval, ihf, ihl]

/-- Every observation of every arbitrary parameter assignment has one finite
profile on these expression atoms. Classical decisions occur only in this
existence proof; the canonical encoder below uses no semantic oracle. -/
theorem observation_has_profile (leRow : Row → Row → Prop) (rank : Nat)
    (env : Environment Row) (observation : Observation Row) (nontrivial : observation ≠ .trivial)
    (parameters : Fin n → StructuralBase.Ty Row) :
    ∃ profile ∈ profiles n, ∀ expression : Expr n,
      ProbeAt leRow rank env (expression.embed parameters) observation ↔ expression.eval profile = true := by
  classical
  let profile := (atoms n).filter fun atom => decide (ProbeAt leRow rank env (atom.embed parameters) observation)
  refine ⟨profile, (mem_profiles profile).mpr List.filter_sublist, ?_⟩
  apply probe_embed_exact leRow rank env observation nontrivial parameters profile
  intro atom
  simp [profile]

/-- All shared variables range over arbitrary contextual producers; no
restriction to finite rigid demands or bottom/top instances appears here. -/
theorem equivalent_iff_evaluations (leRow : Row → Row → Prop) (first last : Expr n) :
    Equivalent leRow first last ↔
      ∀ profile ∈ profiles n, first.eval profile = last.eval profile := by
  constructor
  · intro same profile _
    apply Bool.eq_iff_iff.mpr
    have observed := (producerEq_iff_probe _ _).mp (same (roleParameters Row profile))
      0 (roleEnvironment Row profile) (.role 0)
    simpa only [eval_role_exact] using observed
  · intro same parameters
    apply (producerEq_iff_probe _ _).mpr
    intro rank env observation
    by_cases trivial : observation = .trivial
    · subst observation
      simp
    · obtain ⟨profile, member, exact⟩ :=
        observation_has_profile leRow rank env observation trivial parameters
      rw [exact first, exact last, same profile member]

def truthTable (expression : Expr n) : List Bool := (profiles n).map expression.eval

theorem truthTable_eq_iff (first last : Expr n) :
    truthTable first = truthTable last ↔
      ∀ profile ∈ profiles n, first.eval profile = last.eval profile :=
  List.map_inj_left

/-- A finite executable complete code for the universal parameter family.
Its size is exponential in the number of variable slots; this reference
encoder makes no efficient-interface or regular-graph claim. -/
theorem truthTable_exact (leRow : Row → Row → Prop) (first last : Expr n) :
    Equivalent leRow first last ↔ truthTable first = truthTable last := by
  rw [equivalent_iff_evaluations, truthTable_eq_iff]

end Yulang.ProducerCanonicalOpen
