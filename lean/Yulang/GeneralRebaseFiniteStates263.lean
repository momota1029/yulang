import Yulang.GeneralRebaseStep258
import Yulang.GeneralRebaseSourceCenters263
namespace Yulang.GeneralRebaseFiniteStates263
open GeneralRebaseStep258

def skip (fact : Fact) {basis : List Fact} (state : State basis) : State (fact :: basis) :=
 ⟨state.remaining,state.canonical.cons fact⟩

def keep (fact : Fact) {basis : List Fact} (state : State basis) : State (fact :: basis) :=
 ⟨fact :: state.remaining,state.canonical.cons_cons fact⟩

/-- Explicit exponential enumeration, retaining duplicates when the basis has
repeated facts. This is not a claim of efficient observer execution. -/
def states : (basis : List Fact) → List (State basis)
 | [] => [done []]
 | fact :: rest => (states rest).map (skip fact) ++ (states rest).map (keep fact)

theorem mem_of_sublist (remaining basis : List Fact) (canonical : remaining.Sublist basis) :
 (⟨remaining,canonical⟩ : State basis) ∈ states basis := by
 induction canonical with
 | slnil => exact List.mem_singleton_self _
 | @cons remaining basis fact canonical ih =>
   exact List.mem_append_left _ (List.mem_map.mpr ⟨⟨remaining,canonical⟩,ih,rfl⟩)
 | @cons_cons remaining basis fact canonical ih =>
   exact List.mem_append_right _ (List.mem_map.mpr ⟨⟨remaining,canonical⟩,ih,rfl⟩)

theorem complete (basis : List Fact) (state : State basis) : state ∈ states basis :=
 mem_of_sublist state.remaining basis state.canonical

theorem length (basis : List Fact) : (states basis).length = 2 ^ basis.length := by
 induction basis with
 | nil => rfl
 | cons fact rest ih =>
   simp only [states,List.length_append,List.length_map,ih,List.length_cons,Nat.pow_succ]
   omega

/-- Every inspector image is represented by this finite list; no reachability
or semantic assumption is required for this elementary image equality. -/
theorem image_exact (basis : List Fact) (inspect : State basis → α) (value : α) :
 value ∈ (states basis).map inspect ↔ ∃ state, inspect state = value := by
 constructor
 · intro member
   obtain ⟨state,_,equal⟩ := List.mem_map.mp member
   exact ⟨state,equal⟩
 · rintro ⟨state,rfl⟩
   exact List.mem_map.mpr ⟨state,complete basis state,rfl⟩

theorem forall_image_iff (basis : List Fact) (inspect : State basis → α) (predicate : α → Prop) :
 (∀ value ∈ (states basis).map inspect, predicate value) ↔ ∀ state, predicate (inspect state) := by
 constructor
 · intro all state
   exact all (inspect state) (List.mem_map.mpr ⟨state,complete basis state,rfl⟩)
 · intro all value member
   obtain ⟨state,_,rfl⟩ := List.mem_map.mp member
   exact all state
/-- The inspector-wide head premise can be stated over an explicit finite
list. It is still a semantic assumption, not a decision procedure for Heads. -/
theorem heads_image_iff (basis : List Fact)
 (inspect : State basis → GeneralNominalVersionedJournal232.State roles)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 (∀ snapshot ∈ (states basis).map inspect, GeneralRebaseSourceCenters263.Heads snapshot assignment) ↔
 ∀ state, GeneralRebaseSourceCenters263.Heads (inspect state) assignment :=
 forall_image_iff basis inspect (fun snapshot => GeneralRebaseSourceCenters263.Heads snapshot assignment)
end Yulang.GeneralRebaseFiniteStates263
