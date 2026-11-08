import Yulang.CommonRoleCandidateStateFrontier

/-! Explicit source-node identities connect different endpoint occurrence slots.
These names are supplied by the source graph, not inferred from type equality.
Only type components are equated; effect components are not identified. -/
namespace Yulang.CommonRoleSourceIdentity
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)

abbrev Table := List Nat
abbrev Slot (table : Table) := Fin table.length

def source (table : Table) (slot : Slot table) : Nat := table[slot.val]

def pairAtoms (left right : Fin n) : List (Atom (Fin n)) :=
  [.tyLe (.var left) (.var right), .tyLe (.var right) (.var left)]

theorem pair_exact (left right : Fin n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (pairAtoms left right) ↔
      Common.Equivalent (assignment left).1 (assignment right).1 := by
  simp [All, pairAtoms, PresenceNormalForm.Atom.Holds, TyTerm.eval,
    Common.model, Common.Equivalent]

def atoms (table : Table) : List (Atom (Slot table)) :=
  (List.finRange table.length).flatMap fun left =>
    (List.finRange table.length).flatMap fun right =>
      if source table left = source table right then pairAtoms left right else []

def Coherent (table : Table) (assignment : Slot table → Comp Common.model) : Prop :=
  ∀ left right, source table left = source table right →
    Common.Equivalent (assignment left).1 (assignment right).1

theorem mem_atoms (table : Table) (atom : Atom (Slot table)) :
    atom ∈ atoms table ↔ ∃ left right : Slot table,
      source table left = source table right ∧ atom ∈ pairAtoms left right := by
  simp [atoms]

theorem atoms_exact (table : Table) (assignment : Slot table → Comp Common.model) :
    All Common.model assignment (atoms table) ↔ Coherent table assignment := by
  constructor
  · intro h left right same
    apply (pair_exact left right assignment).mp
    intro atom member
    exact h atom ((mem_atoms table atom).mpr ⟨left, right, same, member⟩)
  · intro h atom member
    obtain ⟨left, right, same, member⟩ := (mem_atoms table atom).mp member
    exact (pair_exact left right assignment).mpr (h left right same) atom member

/-- Pulling one source valuation back to its occurrences never splits identity. -/
def pullback (table : Table) (valuation : Nat → Comp Common.model) :
    Slot table → Comp Common.model := fun slot => valuation (source table slot)

theorem pullback_coherent (table : Table) (valuation : Nat → Comp Common.model) :
    Coherent table (pullback table valuation) := by
  intro left right same
  simp only [pullback, same]
  exact Common.equivalent_refl _

theorem pullback_satisfies (table : Table) (valuation : Nat → Comp Common.model) :
    All Common.model (pullback table valuation) (atoms table) :=
  (atoms_exact _ _).mpr (pullback_coherent _ _)

theorem pair_grammar (left right : Fin n) :
    PresenceGeneratedChildGrammar.GoodAtoms (pairAtoms left right) ∧
    PresenceGeneratedWidth.WidthAtoms (pairAtoms left right) ∧
    PresenceSourceConstraintSupport.GoodAtoms (pairAtoms left right) := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    simp only [pairAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  · intro source target member tail needed
    simp only [pairAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with h | h <;> cases h <;> cases needed
  · intro atom member
    simp only [pairAtoms, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial

theorem atoms_grammar (table : Table) :
    PresenceGeneratedChildGrammar.GoodAtoms (atoms table) ∧
    PresenceGeneratedWidth.WidthAtoms (atoms table) ∧
    PresenceSourceConstraintSupport.GoodAtoms (atoms table) := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    obtain ⟨left, right, _, pair⟩ := (mem_atoms table atom).mp member
    exact (pair_grammar left right).1 atom pair
  · intro source target member tail needed
    obtain ⟨left, right, same, pair⟩ := (mem_atoms table _).mp member
    exact (mem_atoms table _).mpr ⟨left, right, same,
      (pair_grammar left right).2.1 source target pair tail needed⟩
  · intro atom member
    obtain ⟨left, right, _, pair⟩ := (mem_atoms table atom).mp member
    exact (pair_grammar left right).2.2 atom pair

def extend (table : Table) (state : State table.length) : State table.length :=
  let g := atoms_grammar table
  ⟨state.atoms ++ atoms table, state.child.append g.1,
    state.width.append g.2.1, state.rows.append g.2.2⟩

theorem extend_exact (table : Table) (state : State table.length)
    (assignment : Slot table → Comp Common.model) :
    All Common.model assignment (extend table state).atoms ↔
      All Common.model assignment state.atoms ∧ Coherent table assignment := by
  change All Common.model assignment (state.atoms ++ atoms table) ↔ _
  rw [PresenceNormalForm.all_append, atoms_exact]

/-- The actual ordinary solver checks shared identities jointly with the old state. -/
theorem consistent_exact (table : Table) (state : State table.length) :
    CommonRoleOpenPropagation.consistent (extend table state) = true ↔
      ∃ assignment : Slot table → Comp Common.model,
        All Common.model assignment state.atoms ∧ Coherent table assignment := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr fun assignment => extend_exact table state assignment

/-- Distinct occurrences of the same source node have equivalent type values
in every model of the extended state, even when their slots differ. -/
theorem shared_source_equivalent (table : Table) (state : State table.length)
    (assignment : Slot table → Comp Common.model)
    (models : All Common.model assignment (extend table state).atoms)
    (left right : Slot table) (same : source table left = source table right) :
    Common.Equivalent (assignment left).1 (assignment right).1 :=
  ((extend_exact ..).mp models).2 left right same

/-- Feasibility is transported between distinct occurrence slots with one
source identity. This is a solver-facing bridge, not merely a table equality. -/
theorem fits_shared_source (table : Table) (state : State table.length)
    (left right : Slot table) (same : source table left = source table right)
    (candidate : CommonRoleCandidateStateFrontier.Candidate) :
    CommonRoleCandidateStateFrontier.Fits (extend table state) left candidate ↔
      CommonRoleCandidateStateFrontier.Fits (extend table state) right candidate := by
  constructor
  · rintro ⟨assignment, models, fits⟩
    have share := shared_source_equivalent table state assignment models left right same
    exact ⟨assignment, models, Common.equivalent_trans (Common.equivalent_symm share) fits⟩
  · rintro ⟨assignment, models, fits⟩
    have share := shared_source_equivalent table state assignment models left right same
    exact ⟨assignment, models, Common.equivalent_trans share fits⟩

/-- An equation arriving at one occurrence constrains candidates tested at a
different occurrence of the same source. It does not arise from candidate uniqueness. -/
theorem fits_after_shared_equation (table : Table) (state : State table.length)
    (left right : Slot table) (same : source table left = source table right)
    (head : Inference.Base) (candidate : CommonRoleCandidateStateFrontier.Candidate) :
    CommonRoleCandidateStateFrontier.Fits
      (CommonRoleCandidateStateFrontier.extend (extend table state) right head) left candidate ↔
      CommonRoleCandidateStateFrontier.Fits (extend table state) left candidate ∧
      head = candidate.head := by
  constructor
  · rintro ⟨assignment, models, fits⟩
    obtain ⟨old, equation⟩ := (CommonRoleCandidateStateFrontier.extend_exact ..).mp models
    have share := shared_source_equivalent table state assignment old left right same
    have equal := Common.equivalent_trans (Common.equivalent_symm equation)
      (Common.equivalent_trans (Common.equivalent_symm share) fits)
    exact ⟨⟨assignment, old, fits⟩, (CommonRigidHeadInspection.base_iff _ _).mp equal.1⟩
  · rintro ⟨⟨assignment, old, fits⟩, sameHead⟩
    subst head
    have share := shared_source_equivalent table state assignment old left right same
    exact ⟨assignment, (CommonRoleCandidateStateFrontier.extend_exact ..).mpr
      ⟨old, Common.equivalent_trans (Common.equivalent_symm share) fits⟩, fits⟩

/-- Old occurrence identities survive extending the finite table. This is
allocation stability, not dynamic-child closure of the complete resolver. -/
def retain (table extra : Table) (slot : Slot table) : Slot (table ++ extra) :=
  ⟨slot.val, by simp only [List.length_append]; omega⟩

theorem retain_source (table extra : Table) (slot : Slot table) :
    source (table ++ extra) (retain table extra slot) = source table slot := by
  simp [source, retain, List.getElem_append_left]

theorem retain_shared (table extra : Table) (left right : Slot table) :
    source (table ++ extra) (retain table extra left) =
      source (table ++ extra) (retain table extra right) ↔
      source table left = source table right := by
  rw [retain_source, retain_source]

end Yulang.CommonRoleSourceIdentity
