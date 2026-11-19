import Yulang.GeneralRebaseActualArguments269
import Yulang.FiniteWorklist

namespace Yulang.GeneralRebaseSlotInequalities269
open GeneralNominalState (State Models)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)
open CommonNominalFullCarrier
open FiniteWorklist (Path reachable)

def pairOf : Atom α → Option (α × α)
 | .tyLe (.var a) (.var b) => some (a,b)
 | _ => none

theorem pair_eq (seen : pairOf atom = some (a,b)) : atom = .tyLe (.var a) (.var b) := by
 cases atom with
 | rowLe => cases seen
 | tyLe first last =>
   cases first <;> cases last <;> cases seen <;> rfl

def listed (state : State) (a b : Fin state.base.slots) : Bool :=
 (state.base.source a == state.base.source b) ||
 state.base.intervals.contains (a,b) ||
 (state.base.ordinary.filterMap pairOf).contains (a,b) ||
 (state.ordinary.filterMap pairOf).contains (state.base.source a,state.base.source b)

def Bound (state : State) (a b : Fin state.base.slots) : Prop :=
 ∀ model, Models state model → Subtype (model (state.base.source a)).1 (model (state.base.source b)).1

theorem by_atom (model : α → Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) (seen : pairOf atom = some (a,b))
 (holds : atom.Holds CommonNominalFullCarrier.model model) :
 Subtype (model a).1 (model b).1 := by
 rw [pair_eq seen] at holds
 exact holds

theorem listed_sound (state : State) (a b : Fin state.base.slots) (yes : listed state a b = true) :
 Bound state a b := by
 intro model valid
 simp only [listed,Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem,List.mem_filterMap] at yes
 rcases yes with (((eq | interval) | ⟨atom,member,inPair⟩) | ⟨atom,member,inPair⟩)
 · rw [eq]
   exact subtype_refl _
 · exact valid.1.2.2 _ interval
 · exact by_atom (GeneralNominalCommonBridge.assignment state.base model) inPair (valid.1.1 _ member)
 · exact by_atom model inPair (valid.2.2 _ member)

def adj (state : State) (a : Fin state.base.slots) : List (Fin state.base.slots) :=
 (List.finRange state.base.slots).filter (listed state a)

def prove (state : State) (a b : Fin state.base.slots) : Bool :=
 decide (b ∈ reachable (adj state) state.base.slots a)

theorem path_sound (state : State) {a b : Fin state.base.slots} (walk : Path (adj state) a b) : Bound state a b := by
 intro model valid
 induction walk with
 | nil => exact subtype_refl _
 | cons hit _ ih =>
   have raw := (List.mem_filter.mp hit).2
   exact subtype_trans (listed_sound state _ _ raw model valid) ih

theorem prove_sound (state : State) (a b : Fin state.base.slots) (yes : prove state a b = true) : Bound state a b := by
 apply path_sound state
 apply (FiniteWorklist.reachable_exact (adj state) state.base.slots (List.finRange state.base.slots)
   (by simp) (by simp) a b).mp
 exact of_decide_eq_true yes

end Yulang.GeneralRebaseSlotInequalities269
