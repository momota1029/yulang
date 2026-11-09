import Yulang.CommonRoleDynamicIndexEqualitySource

/-! Semantic completeness of the finite string/equality adapter. A separating
model assigns int to unreachable slots; this is not general source inference. -/
namespace Yulang.CommonRoleDynamicIndexSemanticSource
open CommonRoleSourceIdentity (Table Slot source)
open CommonRoleSettledConstraints (State)
open CommonRoleDynamicIndexSource (Requests)
open CommonRoleDynamicIndexEqualitySource (Links initial output Derived saturate)
open CommonRoleOrdinaryKnownness (Evidence)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

private theorem addEqualities_contains (s : State n) (links : List (Fin n × Fin n))
    (atom : PresenceNormalForm.Atom (Fin n)) (h : atom ∈ s.atoms) :
    atom ∈ (CommonRoleDynamicIndexConsistentSource.addEqualities s links).atoms := by
  induction links with
  | nil => exact h
  | cons e rest ih => exact List.mem_append_left _ ih

theorem seed_derived (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i : Slot table) (hi : i ∈ seeds) :
    Derived table seeds links requests i := by
  apply Derived.seed
  have he := CommonRoleDynamicIndexClosure.record_evidence State.empty seeds i hi
  constructor
  · exact List.mem_append_left _ (addEqualities_contains _ links _ he.1)
  · exact List.mem_append_left _ (addEqualities_contains _ links _ he.2)

theorem alias_derived_iff (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i j : Slot table) (h : source table i = source table j) :
    Derived table seeds links requests i ↔ Derived table seeds links requests j :=
  ⟨Derived.alias h, Derived.alias h.symm⟩

theorem equality_derived_iff (table : Table) (seeds : List (Slot table)) (links : Links table)
    (requests : Requests) (i j : Slot table) (h : (i,j) ∈ links) :
    Derived table seeds links requests i ↔ Derived table seeds links requests j :=
  ⟨Derived.equality (.inl h), Derived.equality (.inr h)⟩

/-- A concrete separating model; effects are empty in every slot. -/
noncomputable def separatingAssignment (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) : Slot table → Comp Common.model := by
  classical
  exact fun i => (if Derived table seeds links requests i then .base .str else .base .int,
    Common.rowEmpty)

theorem separatingAssignment_models (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) :
    All Common.model (separatingAssignment table seeds links requests)
      (output table seeds links requests).atoms := by
  classical
  apply (CommonRoleDynamicIndexEqualitySource.output_models ..).mpr
  constructor
  · apply (CommonRoleDynamicIndexEqualitySource.initial_models ..).mpr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i hi
      simpa [separatingAssignment, seed_derived table seeds links requests i hi]
        using Common.equivalent_refl (.base .str)
    · intro e he
      have hd := equality_derived_iff table seeds links requests e.1 e.2 he
      change Common.Equivalent (if Derived table seeds links requests e.1 then _ else _)
        (if Derived table seeds links requests e.2 then _ else _)
      rw [hd]
      exact Common.equivalent_refl _
    · intro i j he
      have hd := alias_derived_iff table seeds links requests i j he
      change Common.Equivalent (if Derived table seeds links requests i then _ else _)
        (if Derived table seeds links requests j then _ else _)
      rw [hd]
      exact Common.equivalent_refl _
  · intro i hi
    simpa [separatingAssignment, hi] using Common.equivalent_refl (.base .str)

/-- Every unreachable slot has an actual output model in which it is int. -/
theorem unreachable_countermodel (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table)
    (hi : ¬ Derived table seeds links requests i) :
    ∃ a : Slot table → Comp Common.model,
      All Common.model a (output table seeds links requests).atoms ∧
      (a i).1 = .base .int := by
  exact ⟨separatingAssignment table seeds links requests,
    separatingAssignment_models table seeds links requests, by simp [separatingAssignment, hi]; rfl⟩

/-- Semantic forcing is exactly finite derivability, for this constructed fragment. -/
theorem forces_str_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table) :
    (∀ a : Slot table → Comp Common.model,
      All Common.model a (output table seeds links requests).atoms →
      Common.Equivalent (a i).1 (.base .str)) ↔ Derived table seeds links requests i := by
  constructor
  · intro h
    classical
    by_cases hd : Derived table seeds links requests i
    · exact hd
    apply False.elim
    have hn := hd
    obtain ⟨a, ha, he⟩ := unreachable_countermodel table seeds links requests i hn
    have hb := (h a ha).1
    rw [he] at hb
    have bad := (CommonRigidHeadInspection.base_iff .int .str).mp hb
    cases bad
  · intro hi a ha
    exact ((CommonRoleDynamicIndexEqualitySource.output_models ..).mp ha).2 i hi

/-- The actual evidence reader is complete for semantic string forcing here. -/
theorem detect_str_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table) :
    CommonRoleOrdinaryKnownness.detect (output table seeds links requests).atoms i = some .str ↔
      Derived table seeds links requests i := by
  constructor
  · intro h
    apply (forces_str_iff ..).mp
    intro a ha
    exact CommonRoleOrdinaryKnownness.detect_sound _ i .str h a ha
  · intro hi
    apply CommonRoleDynamicIndexClosure.detects_recorded
      (initial table seeds links) (saturate table seeds links requests) i
      ((CommonRoleDynamicIndexEqualitySource.saturate_exact ..).mpr hi)
      CommonRoleDynamicIndexConsistentSource.stringAssignment
    exact CommonRoleDynamicIndexEqualitySource.output_has_model table seeds links requests

/-- No other scalar can be read from this consistent all-string fragment. -/
theorem detected_base_str (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table) (b : Inference.Base)
    (h : CommonRoleOrdinaryKnownness.detect (output table seeds links requests).atoms i = some b) :
    b = .str := by
  have he := CommonRoleOrdinaryKnownness.detect_sound _ i b h
    CommonRoleDynamicIndexConsistentSource.stringAssignment
    (CommonRoleDynamicIndexEqualitySource.output_has_model table seeds links requests)
  exact ((CommonRigidHeadInspection.base_iff .str b).mp he.1).symm

theorem detect_none_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table) :
    CommonRoleOrdinaryKnownness.detect (output table seeds links requests).atoms i = none ↔
      ¬ Derived table seeds links requests i := by
  constructor
  · intro hn hd
    have hs := (detect_str_iff table seeds links requests i).mpr hd
    rw [hn] at hs
    cases hs
  · intro hn
    cases h : CommonRoleOrdinaryKnownness.detect (output table seeds links requests).atoms i with
    | none => rfl
    | some b =>
      have hb := detected_base_str table seeds links requests i b h
      subst b
      exact False.elim (hn ((detect_str_iff ..).mp h))

/-- Missing evidence is genuine underdetermination, not an inconsistent state. -/
theorem produce_none_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table) :
    CommonRoleOrdinaryKnownness.produceIndex (output table seeds links requests) i j = none ↔
      ¬ Derived table seeds links requests i := by
  constructor
  · intro hn hi
    have hs := CommonRoleOrdinaryKnownness.index_from_detected_str
      (output table seeds links requests) i j ((detect_str_iff ..).mpr hi)
    rw [hn] at hs
    cases hs
  · intro hn
    have hd := (detect_none_iff table seeds links requests i).mpr hn
    simp [CommonRoleOrdinaryKnownness.produceIndex,
      CommonRoleOrdinaryKnownness.materialize, hd]

/-- The checked producer succeeds exactly for derived receivers. This is not
language-visible classification, and j need not be a source-request edge. -/
theorem checked_success_iff (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i j : Slot table) :
    (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (output table seeds links requests) i j = some out) ↔
      Derived table seeds links requests i := by
  constructor
  · rintro ⟨out, ho⟩
    classical
    by_cases hd : Derived table seeds links requests i
    · exact hd
    apply False.elim
    have hn := hd
    have hp := (CommonRoleOrdinaryKnownness.checked_exact ..).mp ho
    rw [(produce_none_iff table seeds links requests i j).mpr hn] at hp
    cases hp.1
  · intro hi
    exact ⟨_, CommonRoleDynamicIndexEqualitySource.reachable_checked_step
      table seeds links requests i j hi⟩

/-- The pending receiver has two distinguishable output models, not merely
an absent syntactic witness. Both assignments are actual models of the output. -/
theorem unreachable_underdetermined (table : Table) (seeds : List (Slot table))
    (links : Links table) (requests : Requests) (i : Slot table)
    (hi : ¬ Derived table seeds links requests i) :
    ∃ a b : Slot table → Comp Common.model,
      All Common.model a (output table seeds links requests).atoms ∧
      All Common.model b (output table seeds links requests).atoms ∧
      ¬ Common.Equivalent (a i).1 (b i).1 := by
  obtain ⟨a, ha, he⟩ := unreachable_countermodel table seeds links requests i hi
  refine ⟨a, CommonRoleDynamicIndexConsistentSource.stringAssignment, ha,
    CommonRoleDynamicIndexEqualitySource.output_has_model table seeds links requests, ?_⟩
  intro h
  have hh := h.1
  change Common.Subtype (a i).1 (.base .str) at hh
  rw [he] at hh
  have bad := (CommonRigidHeadInspection.base_iff .int .str).mp hh
  cases bad

end Yulang.CommonRoleDynamicIndexSemanticSource
