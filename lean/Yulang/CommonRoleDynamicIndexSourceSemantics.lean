import Yulang.CommonRoleDynamicIndexSemanticSource

/-! Independent source-model semantics for the finite positive string fragment.
The clauses do not refer to saturation or its output. Other payloads, arbitrary
initial states, source parsing, and final language classification are outside this
fragment. Conditional request clauses are not serialized into ordinary atoms. -/
namespace Yulang.CommonRoleDynamicIndexSourceSemantics
open CommonRoleSourceIdentity (Table Slot source Coherent)
open CommonRoleDynamicIndexSource (Requests)
open CommonRoleDynamicIndexEqualitySource (Links initial output Derived)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

/-- The positive string consequence semantics. Every named occurrence pair is
covered, including aliases. This is not the full semantics of Index on all types. -/
structure SourceModel (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (a : Slot table → Comp Common.model) : Prop where
  seeds : ∀ i ∈ seeds, Common.Equivalent (a i).1 (.base .str)
  equalities : ∀ e ∈ links, Common.Equivalent (a e.1).1 (a e.2).1
  aliases : Coherent table a
  requests : ∀ i j, (source table i, source table j) ∈ requests →
    Common.Equivalent (a i).1 (.base .str) → Common.Equivalent (a j).1 (.base .str)

/-- Quantification is over source models, with no executable output in the type. -/
def ForcesString (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i : Slot table) : Prop :=
  ∀ a : Slot table → Comp Common.model,
    SourceModel table seeds links requests a → Common.Equivalent (a i).1 (.base .str)

theorem source_models_initial (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (a : Slot table → Comp Common.model)
    (hm : SourceModel table seeds links requests a) :
    All Common.model a (initial table seeds links).atoms :=
  (CommonRoleDynamicIndexEqualitySource.initial_models ..).mpr
    ⟨⟨hm.seeds, hm.equalities⟩, hm.aliases⟩

/-- Soundness of all four independent rules against the source clauses. -/
theorem derived_sound (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i : Slot table) (hi : Derived table seeds links requests i) :
    ForcesString table seeds links requests i := by
  intro a hm
  induction hi with
  | seed h =>
    exact CommonRoleOrdinaryKnownness.evidence_models _ _ _ h a
      (source_models_initial table seeds links requests a hm)
  | @alias i j h _ ih =>
    exact Common.equivalent_trans (Common.equivalent_symm (hm.aliases i j h)) ih
  | @equality i j h _ ih =>
    rcases h with h | h
    · exact Common.equivalent_trans (Common.equivalent_symm (hm.equalities (i,j) h)) ih
    · exact Common.equivalent_trans (hm.equalities (j,i) h) ih
  | index h _ ih => exact hm.requests _ _ h ih

/-- Source models satisfy the computed output atoms. The reverse is not claimed:
unresolved conditional requests are not represented by those atoms. -/
theorem source_models_output (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (a : Slot table → Comp Common.model)
    (hm : SourceModel table seeds links requests a) :
    All Common.model a (output table seeds links requests).atoms :=
  (CommonRoleDynamicIndexEqualitySource.output_models ..).mpr
    ⟨source_models_initial table seeds links requests a hm,
      fun i hi => derived_sound table seeds links requests i hi a hm⟩

/-- A concrete model of the independent clauses separates every unreachable slot. -/
theorem separating_source_model (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) :
    SourceModel table seeds links requests
      (CommonRoleDynamicIndexSemanticSource.separatingAssignment table seeds links requests) := by
  classical
  have hm := (CommonRoleDynamicIndexEqualitySource.output_models ..).mp
    (CommonRoleDynamicIndexSemanticSource.separatingAssignment_models table seeds links requests)
  have hi := (CommonRoleDynamicIndexEqualitySource.initial_models ..).mp hm.1
  refine ⟨hi.1.1, hi.1.2, hi.2, ?_⟩
  intro i j he hs
  have di : Derived table seeds links requests i := by
    by_cases hn : Derived table seeds links requests i
    · exact hn
    apply False.elim
    have bad := hs.1
    simp only [CommonRoleDynamicIndexSemanticSource.separatingAssignment, hn, ↓reduceIte] at bad
    have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp bad
    cases impossible
  exact hm.2 j (Derived.index he di)

theorem string_source_model (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) :
    SourceModel table seeds links requests CommonRoleDynamicIndexConsistentSource.stringAssignment := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _ _; exact Common.equivalent_refl _
  · intro _ _; exact Common.equivalent_refl _
  · intro _ _ _; exact Common.equivalent_refl _
  · intro _ _ _ _; exact Common.equivalent_refl _

/-- Completeness against a source semantics independent of the executable atoms. -/
theorem source_forces_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table) :
    ForcesString table seeds links requests i ↔ Derived table seeds links requests i := by
  constructor
  · intro h
    classical
    by_cases hn : Derived table seeds links requests i
    · exact hn
    apply False.elim
    have bad := (h _ (separating_source_model table seeds links requests)).1
    simp only [CommonRoleDynamicIndexSemanticSource.separatingAssignment, hn, ↓reduceIte] at bad
    have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp bad
    cases impossible
  · exact derived_sound table seeds links requests i

/-- Both presentations have exactly the same string consequences, even though
conditional source models and output-atom models are not the same model class. -/
theorem source_output_forcing_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table) :
    ForcesString table seeds links requests i ↔
      (∀ a : Slot table → Comp Common.model,
        All Common.model a (output table seeds links requests).atoms →
        Common.Equivalent (a i).1 (.base .str)) :=
  (source_forces_iff ..).trans (CommonRoleDynamicIndexSemanticSource.forces_str_iff ..).symm

/-- The real checked producer succeeds exactly when independent source models
force its receiver to string. j is arbitrary; no request-membership premise. -/
theorem checked_source_exact (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table) :
    (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (output table seeds links requests) i j = some out) ↔
      ForcesString table seeds links requests i :=
  (CommonRoleDynamicIndexSemanticSource.checked_success_iff ..).trans (source_forces_iff ..).symm

/-- Missing string forcing is witnessed by two actual source models. -/
theorem source_underdetermined_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table) :
    (∃ a b : Slot table → Comp Common.model,
      SourceModel table seeds links requests a ∧ SourceModel table seeds links requests b ∧
      ¬ Common.Equivalent (a i).1 (b i).1) ↔ ¬ ForcesString table seeds links requests i := by
  constructor
  · rintro ⟨a,b,ha,hb,ne⟩ h
    exact ne (Common.equivalent_trans (h a ha) (Common.equivalent_symm (h b hb)))
  · intro hn
    have hd : ¬ Derived table seeds links requests i := fun h => hn ((source_forces_iff ..).mpr h)
    refine ⟨CommonRoleDynamicIndexSemanticSource.separatingAssignment table seeds links requests,
      CommonRoleDynamicIndexConsistentSource.stringAssignment,
      separating_source_model table seeds links requests,
      string_source_model table seeds links requests, ?_⟩
    intro h
    have bad := h.1
    simp only [CommonRoleDynamicIndexSemanticSource.separatingAssignment, hd, ↓reduceIte] at bad
    have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp bad
    cases impossible


/-- The actual checked producer is pending exactly when independent source
models disagree on the receiver. No inconsistent-state alternative is hidden. -/
theorem checked_pending_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table) :
    CommonRoleOrdinaryKnownness.checkedProduceIndex
      (output table seeds links requests) i j = none ↔
    (∃ a b : Slot table → Comp Common.model,
      SourceModel table seeds links requests a ∧ SourceModel table seeds links requests b ∧
      ¬ Common.Equivalent (a i).1 (b i).1) := by
  rw [source_underdetermined_iff]
  constructor
  · intro hn hf
    obtain ⟨out, ho⟩ := (checked_source_exact table seeds links requests i j).mpr hf
    rw [hn] at ho
    cases ho
  · intro hn
    cases h : CommonRoleOrdinaryKnownness.checkedProduceIndex
        (output table seeds links requests) i j with
    | none => rfl
    | some out => exact False.elim (hn ((checked_source_exact ..).mp ⟨out, h⟩))

/-- For an actual named request, successful replay at saturation preserves all
ordinary output models. This is semantic closure, not equality of atom lists. -/
theorem checked_request_models (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table)
    (request : (source table i, source table j) ∈ requests)
    (out : CommonRoleSettledConstraints.State table.length)
    (checked : CommonRoleOrdinaryKnownness.checkedProduceIndex
      (output table seeds links requests) i j = some out)
    (a : Slot table → Comp Common.model) :
    All Common.model a out.atoms ↔ All Common.model a (output table seeds links requests).atoms := by
  have di := (CommonRoleDynamicIndexSemanticSource.checked_success_iff table seeds links requests i j).mp
    ⟨out, checked⟩
  have dj := Derived.index request di
  have step := CommonRoleDynamicIndexEqualitySource.reachable_checked_step table seeds links requests i j di
  rw [checked] at step
  have eq := Option.some.inj step
  rw [eq, CommonRoleCandidateStateFrontier.extend_exact]
  exact ⟨And.left, fun hm => ⟨hm,
    ((CommonRoleDynamicIndexEqualitySource.output_models ..).mp hm).2 j dj⟩⟩


/-- A boundary witness: an unresolved request's conditional clause is absent
from the ordinary output atoms. The two semantic presentations are not equated. -/
theorem output_models_not_source_models :
    ∃ a : Slot [10,20] → Comp Common.model,
      All Common.model a (output [10,20] [] [] [(10,20)]).atoms ∧
      ¬ SourceModel [10,20] [] [] [(10,20)] a := by
  let a : Slot [10,20] → Comp Common.model :=
    fun i => (if i = 0 then .base .str else .base .int, Common.rowEmpty)
  refine ⟨a, ?_, ?_⟩
  · apply (CommonRoleDynamicIndexEqualitySource.output_models ..).mpr
    constructor
    · apply (CommonRoleDynamicIndexEqualitySource.initial_models ..).mpr
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro _ h; cases h
      · intro _ h; cases h
      · intro i j he
        have injective : ∀ i j : Slot [10,20], source [10,20] i = source [10,20] j → i = j := by decide
        rw [injective i j he]
        exact Common.equivalent_refl _
    · intro i hi
      have mem := (CommonRoleDynamicIndexEqualitySource.saturate_exact [10,20] [] [] [(10,20)] i).mpr hi
      have empty : CommonRoleDynamicIndexEqualitySource.saturate [10,20] [] [] [(10,20)] = [] := by decide
      rw [empty] at mem
      cases mem
  · intro hm
    have he := hm.requests 0 1 (by decide) (by simpa [a] using Common.equivalent_refl (.base .str))
    have bad := he.1
    change Common.Subtype (.base .int) (.base .str) at bad
    have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp bad
    cases impossible

end Yulang.CommonRoleDynamicIndexSourceSemantics
