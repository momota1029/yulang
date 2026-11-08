import Yulang.CommonRoleSourceDescent

/-! Conservative extension of independent source occurrence tables.
New occurrences inherit type meaning by source identity; old computation values,
including their effect components, are retained literally. -/
namespace Yulang.CommonRoleSourceGrowth
open CommonRoleSourceIdentity CommonRoleSourceDescent
open Core.PresenceGeneration (Comp)

def restrict (table extra : Table) (values : Slot (table ++ extra) → Comp Common.model) :
    Slot table → Comp Common.model := fun slot => values (retain table extra slot)

def grow (table extra : Table) (values : Slot table → Comp Common.model)
    (fallback : Comp Common.model) : Slot (table ++ extra) → Comp Common.model := fun slot =>
  if h : slot.val < table.length then values ⟨slot.val, h⟩
  else (descend table values fallback.1 (source (table ++ extra) slot), fallback.2)

theorem restrict_grow (table extra : Table) (values : Slot table → Comp Common.model)
    (fallback : Comp Common.model) :
    restrict table extra (grow table extra values fallback) = values := by
  funext slot
  simp [restrict, grow, retain]

theorem restrict_coherent (table extra : Table)
    (values : Slot (table ++ extra) → Comp Common.model)
    (coherent : Coherent (table ++ extra) values) :
    Coherent table (restrict table extra values) := by
  intro left right same
  exact coherent (retain table extra left) (retain table extra right)
    ((retain_shared table extra left right).mpr same)

theorem grow_factors (table extra : Table) (values : Slot table → Comp Common.model)
    (fallback : Comp Common.model) (coherent : Coherent table values) :
    Factors (table ++ extra) (grow table extra values fallback)
      (descend table values fallback.1) := by
  intro slot
  by_cases h : slot.val < table.length
  · have retained : retain table extra ⟨slot.val, h⟩ = slot := by apply Fin.ext; rfl
    have same := retain_source table extra ⟨slot.val, h⟩
    rw [retained] at same
    simpa [grow, h, same] using
      (descend_factors table values fallback.1 coherent ⟨slot.val, h⟩)
  · simp only [grow, dite_eq_right h]
    exact Common.equivalent_refl _

theorem grow_coherent (table extra : Table) (values : Slot table → Comp Common.model)
    (fallback : Comp Common.model) (coherent : Coherent table values) :
    Coherent (table ++ extra) (grow table extra values fallback) :=
  factors_coherent _ _ _ (grow_factors table extra values fallback coherent)

/-- No type-coherent old model is lost by allocating any finite list of new
occurrences, even if new identities repeat old identities. No new ordinary
constraints are asserted by this allocation theorem. -/
theorem extension_exact (table extra : Table) (values : Slot table → Comp Common.model)
    (fallback : Comp Common.model) :
    Coherent table values ↔ ∃ extended : Slot (table ++ extra) → Comp Common.model,
      restrict table extra extended = values ∧ Coherent (table ++ extra) extended := by
  constructor
  · intro coherent
    exact ⟨grow table extra values fallback, restrict_grow table extra values fallback, grow_coherent table extra values fallback coherent⟩
  · rintro ⟨extended, retained, coherent⟩
    rw [← retained]
    exact restrict_coherent table extra extended coherent

/-- Old constraints may be any predicate on full computation valuations. Their
satisfiability with identity atoms is preserved in both directions by table growth. -/
theorem constrained_atoms_exact (table extra : Table)
    (old : (Slot table → Comp Common.model) → Prop) (fallback : Comp Common.model) :
    (∃ values, old values ∧ PresenceNormalForm.All Common.model values (atoms table)) ↔
    ∃ extended, old (restrict table extra extended) ∧
      PresenceNormalForm.All Common.model extended (atoms (table ++ extra)) := by
  simp only [atoms_exact]
  constructor
  · rintro ⟨values, holds, coherent⟩
    obtain ⟨extended, retained, extendedCoherent⟩ :=
      (extension_exact table extra values fallback).mp coherent
    exact ⟨extended, retained ▸ holds, extendedCoherent⟩
  · rintro ⟨extended, holds, coherent⟩
    exact ⟨restrict table extra extended, holds, restrict_coherent table extra extended coherent⟩

/-- Rename every old ordinary atom into its retained slot, then generate the
real identity equations for the expanded occurrence table. -/
def growState (table extra : Table)
    (state : CommonRoleSettledConstraints.State table.length) :
    CommonRoleSettledConstraints.State (table ++ extra).length :=
  extend (table ++ extra)
    ⟨state.atoms.map (PresenceNormalForm.Atom.rename (retain table extra)),
      state.child.rename _, state.width.rename _, state.rows.rename _⟩

theorem growState_models_exact (table extra : Table)
    (state : CommonRoleSettledConstraints.State table.length)
    (values : Slot (table ++ extra) → Comp Common.model) :
    PresenceNormalForm.All Common.model values (growState table extra state).atoms ↔
      PresenceNormalForm.All Common.model (restrict table extra values) state.atoms ∧
      Coherent (table ++ extra) values := by
  rw [growState, extend_exact, PresenceNormalForm.all_rename]
  rfl

/-- The executable ordinary solver accepts exactly the same old constraints
before and after finite source allocation. Arbitrary duplicate source identities
are allowed; new ordinary constraints must be handled separately. -/
theorem solver_growth_exact (table extra : Table)
    (state : CommonRoleSettledConstraints.State table.length)
    (fallback : Comp Common.model) :
    CommonRoleOpenPropagation.consistent (growState table extra state) = true ↔
      CommonRoleOpenPropagation.consistent (extend table state) = true := by
  rw [CommonRoleOpenPropagation.consistent_exact,
    CommonRoleSourceIdentity.consistent_exact]
  change (∃ values, PresenceNormalForm.All Common.model values
    (growState table extra state).atoms) ↔ _
  simp only [growState_models_exact]
  have exactness := constrained_atoms_exact table extra
    (fun values => PresenceNormalForm.All Common.model values state.atoms) fallback
  simpa only [atoms_exact] using exactness.symm

end Yulang.CommonRoleSourceGrowth
