import Yulang.GeneralNominalVersionedAllocation231
/-! Acyclicity of actual content-addressed aggregate dependencies. Every source
on an aggregate right-hand side is strictly below that aggregate's numeric
source. This is neither finite version enumeration nor model amalgamation. -/
namespace Yulang.GeneralNominalVersionedDependency236
open GeneralNominalIdentities GeneralNominalAggregateVersion231
open GeneralNominalAllocation (Bindings occurrences)

theorem pair_left (first last : Nat) : first ≤ pair first last := by
  unfold pair
  omega

theorem pair_right (first last : Nat) : last ≤ pair first last := by
  have bound := Nat.le_mul_self (first + last)
  unfold pair
  omega

theorem position_le (key : Origin) : key.2.2.2.2 ≤ encode key := by
  have a := pair_right key.2.2.2.1 key.2.2.2.2
  have b := pair_right key.2.2.1 (pair key.2.2.2.1 key.2.2.2.2)
  have c := pair_right key.2.1 (pair key.2.2.1 (pair key.2.2.2.1 key.2.2.2.2))
  have d := pair_right key.1 (pair key.2.1 (pair key.2.2.1 (pair key.2.2.2.1 key.2.2.2.2)))
  unfold encode
  omega

theorem endpoint_below_code {values : List GeneralSourceState.Interval}
    (member : bounds ∈ values) : bounds.1 < code values ∧ bounds.2 < code values := by
  induction values with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · have first := pair_left bounds.1 bounds.2
      have outer := pair_left (pair bounds.1 bounds.2) (code tail)
      have last := pair_right bounds.1 bounds.2
      change _ < Nat.succ _ ∧ _ < Nat.succ _
      omega
    · obtain ⟨first,last⟩ := ih member
      have next := pair_right (pair head.1 head.2) (code tail)
      change _ < Nat.succ _ ∧ _ < Nat.succ _
      omega

theorem endpoints_below_slot (seed root declaration purpose name : Nat) (bindings : Bindings)
    (member : bounds ∈ occurrences bindings name) :
    bounds.1 < slot seed root declaration purpose name bindings ∧
      bounds.2 < slot seed root declaration purpose name bindings := by
  obtain ⟨first,last⟩ := endpoint_below_code member
  have bound := position_le (key root declaration purpose name bindings)
  change Nat.succ (code (occurrences bindings name)) ≤ _ at bound
  unfold slot source
  omega

/-- Actual repeated-name capture endpoints lie above every observed endpoint.
Singleton captures deliberately remain the original endpoint pair. -/
theorem repeated_capture_above (state : GeneralNominalState.State) (registry)
    (root declaration name : Nat) (bindings : Bindings)
    (repeated : ∀ bounds, occurrences bindings name ≠ [bounds])
    (member : bounds ∈ occurrences bindings name) :
    bounds.1 < ((GeneralNominalVersionedAllocation231.capture state registry root declaration bindings).inputs name).1 ∧
    bounds.2 < ((GeneralNominalVersionedAllocation231.capture state registry root declaration bindings).inputs name).2 := by
  have lower := endpoints_below_slot state.seed root declaration 0 name bindings member
  have upper := endpoints_below_slot state.seed root declaration 1 name bindings member
  unfold GeneralNominalVersionedAllocation231.capture
  dsimp only
  split
  · rename_i equal
    exact False.elim (repeated _ equal)
  · exact ⟨lower.1,upper.2⟩

/-- An edge records an actual endpoint of an encoded aggregate, not an
arbitrary freshness/independence hypothesis. -/
def Dependency (seed : Nat) (endpoint aggregate : Nat) : Prop :=
  ∃ root declaration purpose name bindings bounds,
    aggregate = slot seed root declaration purpose name bindings ∧
    bounds ∈ occurrences bindings name ∧ (endpoint = bounds.1 ∨ endpoint = bounds.2)

theorem dependency_lt (edge : Dependency seed endpoint aggregate) : endpoint < aggregate := by
  obtain ⟨root,declaration,purpose,name,bindings,bounds,rfl,member,equal⟩ := edge
  have smaller := endpoints_below_slot seed root declaration purpose name bindings member
  rcases equal with rfl | rfl
  · exact smaller.1
  · exact smaller.2

theorem dependency_wellFounded (seed : Nat) : WellFounded (Dependency seed) :=
  Subrelation.wf (fun edge => dependency_lt edge) Nat.lt_wfRel.wf

theorem no_self_dependency (seed source : Nat) : ¬ Dependency seed source source :=
  fun edge => Nat.lt_irrefl _ (dependency_lt edge)
end Yulang.GeneralNominalVersionedDependency236
