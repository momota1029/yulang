import Yulang.CommonRoleOpenPropagation

/-! The capture atoms used by the state pass originate from the actual
selected source declaration and the two original inspected payloads. This
proves the finite slot-level statement, not that Allocation is a source
allocator preserving nominal interpretation or graph provenance. -/
namespace Yulang.CommonRoleOpenPropagationOrigin
open CommonRoleSettledSyntax
open CommonRoleSettledConstraints (State)
open CommonRoleOpenProducer
open CommonRoleOpenPropagation
open CommonRoleCandidateConstraints (Bindings Compatible bounds)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

theorem capture_bounds (allocate : Allocation n) (d : Declaration) (lo up : Ty)
    (name : Nat) (pair : Fin n × Fin n)
    (member : pair ∈ bounds (capture allocate d lo up) name) :
    pair = (allocate lo, allocate up) := by
  obtain ⟨⟨key, pair'⟩, present, found⟩ := List.mem_filterMap.mp member
  obtain ⟨original, _, equal⟩ := List.mem_map.mp present
  cases equal
  split at found <;> simp_all

theorem capture_present (allocate : Allocation n) (d : Declaration) (lo up : Ty)
    (name : Nat) (member : name ∈ d.head.names) :
    (allocate lo, allocate up) ∈ bounds (capture allocate d lo up) name := by
  apply List.mem_filterMap.mpr
  refine ⟨(name, (allocate lo, allocate up)), List.mem_map.mpr ⟨name, member, rfl⟩, ?_⟩
  simp

theorem capture_exact (allocate : Allocation n) (d : Declaration) (lo up : Ty)
    (assignment : Fin n → Comp Common.model) :
    Compatible (capture allocate d lo up) assignment ↔
      d.head.names = [] ∨ Common.Subtype (assignment (allocate lo)).1 (assignment (allocate up)).1 := by
  constructor
  · intro h
    cases names : d.head.names with
    | nil => exact Or.inl rfl
    | cons name rest =>
      right
      have member : name ∈ d.head.names := by simp [names]
      exact h name (by simp [capture, CommonRoleCandidateConstraints.names, names])
        _ (capture_present _ _ _ _ _ member) _ (capture_present _ _ _ _ _ member)
  · rintro (empty | compatible)
    · intro name member
      simp [capture, CommonRoleCandidateConstraints.names, empty] at member
    · intro name _ first present last included
      rw [capture_bounds _ _ _ _ _ _ present, capture_bounds _ _ _ _ _ _ included]
      exact compatible

/-- The update is tied to the actual unique hit, never supplied independently. -/
theorem selected_update_origin (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (key : Nat) (cs : List Request)
    (selected : Local visible q (.selected key cs)) :
    ∃ d lo up, production visible q = some (d, lo, up) ∧ key = d.key ∧
      cs = CommonRoleOpenProducer.children q d lo up ∧
      update visible allocate q = capture allocate d lo up := by
  obtain ⟨d, lo, up, returned, keyEq, childEq⟩ :=
    CommonRoleOpenProducerAccess.selected_production visible q key cs selected
  refine ⟨d, lo, up, returned, keyEq, childEq, ?_⟩
  have selectedEq : frontier visible q = .selected key cs := (frontier_exact visible q _).mpr selected
  rw [update, selectedEq, returned]

/-- On every selected local producer, the exact retained semantic obligation
is the relation between its OWN two allocated captured endpoints. -/
theorem selected_prepare_exact (visible : List Declaration) (allocate : Allocation n)
    (q : Request) (key : Nat) (cs : List Request) (s : State n)
    (selected : Local visible q (.selected key cs)) :
    ∃ d lo up, production visible q = some (d, lo, up) ∧ key = d.key ∧
      cs = CommonRoleOpenProducer.children q d lo up ∧
      ∀ assignment : Fin n → Comp Common.model,
        All Common.model assignment (prepare visible allocate q s).atoms ↔
          All Common.model assignment s.atoms ∧
            (d.head.names = [] ∨ Common.Subtype (assignment (allocate lo)).1 (assignment (allocate up)).1) := by
  obtain ⟨d, lo, up, returned, keyEq, childEq, updateEq⟩ :=
    selected_update_origin visible allocate q key cs selected
  refine ⟨d, lo, up, returned, keyEq, childEq, ?_⟩
  intro assignment
  rw [prepare_exact, updateEq, capture_exact]

end Yulang.CommonRoleOpenPropagationOrigin
