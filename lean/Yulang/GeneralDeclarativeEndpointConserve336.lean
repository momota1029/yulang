import Yulang.GeneralDeclarativeEndpointOverlay336
import Yulang.GeneralDeclarativeOpaqueConserve328
import Yulang.GeneralDeclarativeEndpointSelected336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointConserve336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEndpointOverlay336 (Entry Holds ModelsWith inputs program_eq)
open GeneralDeclarativeEndpointBatch336 (atSlots)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralNominalCommonBridge (Assignment)

def refs (e : Entry) : List Nat :=
  inputs e.1 ++ [e.2.lower,e.2.center,e.2.upper]

def names (es : List Entry) : List Nat :=
  es.flatMap refs

theorem slots_same {e : Entry} {m n : Assignment} (kept : ∀ v ∈ refs e, n v = m v) :
    atSlots n e.2 = atSlots m e.2 := by
  have lo := kept e.2.lower (List.mem_append_right _ List.mem_cons_self)
  have ct := kept e.2.center (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hi := kept e.2.upper (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  simp only [atSlots,lo,ct,hi]

theorem holds_same {e : Entry} {m n : Assignment} (kept : ∀ v ∈ refs e, n v = m v) :
    Holds n e ↔ Holds m e := by
  have src := program_eq (p := e.1) (m := m) (n := n) (fun v inInput =>
    kept v (List.mem_append_left _ inInput))
  unfold Holds
  rw [src,slots_same kept]

theorem receipts_same {rs : List Entry} {m n : Assignment} (kept : ∀ v ∈ names rs, n v = m v) :
    (∀ e ∈ rs, Holds n e) ↔ ∀ e ∈ rs, Holds m e := by
  have valid : ∀ e ∈ rs, Holds n e ↔ Holds m e := by
    intro e part
    exact holds_same (fun n present => kept n (List.mem_flatMap.mpr ⟨e,part,present⟩))
  exact ⟨fun ae e part => (valid e part).mp (ae e part),fun ae e part => (valid e part).mpr (ae e part)⟩

/-- Lift ordinary conservative naming into the projection model
without re-observing old rows. Include the real read footprint in the
preserved set; preserving just the numeric capture ids is not enough. -/
theorem conserve {s t : State} (grow : Retains s t keep)
    (footprint : names rs ⊆ stateNames s ++ keep) (m : Assignment) :
    ModelsWith s rs m ↔ ∃ n, ModelsWith t rs n ∧ ∀ v ∈ stateNames s ++ keep, n v = m v := by
  refine ⟨?_,?_⟩
  · intro valid
    obtain ⟨n,known,kept⟩ := grow.lifts m valid.1
    exact ⟨n,⟨known,(receipts_same (fun v h => kept v (footprint h))).mpr valid.2⟩,kept⟩
  · intro ⟨n,valid,kept⟩
    exact ⟨(GeneralDeclarativeOpaqueConserve328.exact grow m).mpr ⟨n,valid.1,kept⟩,
      (receipts_same (fun v h => kept v (footprint h))).mp valid.2⟩

open GeneralDeclarativeStableAssemble329 (tieState merged assemble)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeEndpointSelected336 (ties_exact)
open GeneralDeclarativeDemand320 (Bounds)

theorem ready_after_ties {s : State} (valid : ModelsWith s rs m) (shared : EqualUses m uses)
    (fit : ∀ slot ∈ uses, Bounds s slot.2)
    (footprint : names rs ⊆ stateNames (tieState s uses fallback) ++ keep) :
    ∃ n, ModelsWith (merged s keep uses fallback).state rs n ∧
      ∀ v ∈ stateNames (tieState s uses fallback) ++ keep, n v = m v := by
  exact (conserve (assemble keep uses fallback fit).preserve footprint m).mp
    ((ties_exact s rs uses fallback m).mpr ⟨valid,shared⟩)

end Yulang.GeneralDeclarativeEndpointConserve336
