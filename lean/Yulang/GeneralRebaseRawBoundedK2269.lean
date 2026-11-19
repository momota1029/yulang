import Yulang.GeneralRebaseIntervalArgument269

namespace Yulang.GeneralRebaseRawBoundedK2269
open GeneralNominalState (State Models)
open GeneralNominalMixedRecurrence (Edge ActualArgument)
open GeneralNominalCycleK2 (RecursAt DirectCycle)
open GeneralRebaseActualArguments269 (TypeSlots Member actual_iff)
open GeneralRebaseIntervalArgument269 (probe probe_sound)
open GeneralRebaseSlotInequalities269 (Bound)
open GeneralRebasePartialCycles268 (Cycle cycle_mono evaluate evaluate_sound)
open GeneralRebasePartialBool268 (Answer Reflect both either)
open GeneralRebasePartialFinite268 (any any_sound transfer)
open GeneralRebaseRawK2Probe268 (bool_reflect mixed_cycle)

def NominalBounded (state : State) (a b : Fin state.base.slots) : Prop :=
 ∃ descriptor, state.nominals a = some descriptor ∧
   ∃ i ∈ TypeSlots descriptor, Member state a b descriptor i.val

def Restricted (state : State) (a b : Fin state.base.slots) : Prop :=
 GeneralSourceK2.Child state.view a b ∨ NominalBounded state a b

theorem bounded_sound (state : State) (a b : Fin state.base.slots)
 (known : NominalBounded state a b) : ActualArgument state a b := by
 obtain ⟨d,rec,i,_,holds⟩ := known
 exact ⟨d,rec,i,holds⟩

theorem bounded_exact (state : State) (model : ∃ model, Models state model)
 (a b : Fin state.base.slots) : NominalBounded state a b ↔ ActualArgument state a b := by
 constructor
 · exact bounded_sound state a b
 · intro actual
   obtain ⟨d,rec,_,_⟩ := Exists.imp (fun x => id) actual
   exact ⟨d,rec,(actual_iff state a b d rec model).mp actual⟩

theorem restricted_cycle_exact (state : State) (a : Fin state.base.slots) :
 Cycle (Restricted state) a ∧ (∃ model, Models state model) ↔
 GeneralNominalCycleK2.Cycle state a ∧ ∃ model, Models state model := by
 constructor
 · rintro ⟨cycled,inhabited⟩
   exact ⟨(mixed_cycle state a).mp
    (cycle_mono (fun x y edge => edge.imp id ((bounded_exact state inhabited x y).mp)) cycled),inhabited⟩
 · rintro ⟨cycled,inhabited⟩
   exact ⟨cycle_mono (fun x y (edge : Edge state x y) => edge.imp id ((bounded_exact state inhabited x y).mpr))
     ((mixed_cycle state a).mpr cycled),inhabited⟩

def nominal (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (parent child : Fin state.base.slots) : Answer :=
 match state.nominals parent with
 | none => some false
 | some d =>
   any (fun i => match d.arguments[i.val] with
     | .type (lo,hi) => probe state bound child lo hi
     | .row _ => some false) (TypeSlots d)

theorem nominal_sound (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (cert : ∀ a b, Reflect (Bound state a b) (bound a b)) (parent child : Fin state.base.slots) :
 Reflect (NominalBounded state parent child) (nominal state bound parent child) := by
 unfold nominal
 split
 · rename_i absent
   rintro ⟨d,rec,_⟩
   rw [absent] at rec
   cases rec
 · rename_i d rec
   apply transfer (p := ∃ i ∈ TypeSlots d, Member state parent child d i.val)
   · constructor
     · exact fun h => ⟨d,rec,h⟩
     · rintro ⟨old,oldRec,h⟩
       cases Option.some.inj (oldRec.symm.trans rec)
       exact h
   · apply any_sound
     intro i inside
     cases located : d.arguments[i.val] with
     | row r =>
       simp [TypeSlots,located] at inside
     | type pair =>
       rcases pair with ⟨lo,hi⟩
       exact probe_sound state bound cert parent child d rec i.val lo hi
         ((List.getElem?_eq_getElem i.isLt).trans (congrArg some located))

def edge (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (a b : Fin state.base.slots) : Answer :=
 either (some (decide (b ∈ CommonRoleRegularGraph.successors state.view.graph a))) (nominal state bound a b)

theorem edge_sound (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (cert : ∀ a b, Reflect (Bound state a b) (bound a b)) (a b : Fin state.base.slots) :
 Reflect (Restricted state a b) (edge state bound a b) :=
 GeneralRebasePartialBool268.either_sound
   (bool_reflect _ _ (by simpa only [decide_eq_true_eq] using
       (GeneralSourceK2.child_graph_iff state.view a b).symm))
   (nominal_sound state bound cert a b)

def recurs (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (model : Answer) (a : Fin state.base.slots) : Answer :=
 either (some (GeneralRebaseDirectCycles268.cycle state a)) (both (evaluate (edge state bound) a) model)

theorem recurs_sound (state : State) (bound : Fin state.base.slots → Fin state.base.slots → Answer)
 (cert : ∀ a b, Reflect (Bound state a b) (bound a b))
 (model : Answer) (modelSound : Reflect (∃ m, Models state m) model) (a : Fin state.base.slots) :
 Reflect (RecursAt state a) (recurs state bound model a) :=
 GeneralRebasePartialBool268.either_sound (bool_reflect _ _ (GeneralRebaseDirectCycles268.cycle_exact state a))
   (transfer (restricted_cycle_exact state a)
     (GeneralRebasePartialBool268.both_sound (evaluate_sound _ _ (edge_sound state bound cert) a) modelSound))

end Yulang.GeneralRebaseRawBoundedK2269
