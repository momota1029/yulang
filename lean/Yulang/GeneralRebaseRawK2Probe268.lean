import Yulang.GeneralRebasePartialFinite268
import Yulang.GeneralRebasePartialCycles268
import Yulang.GeneralRebaseDirectedRoot268

namespace Yulang.GeneralRebaseRawK2Probe268
open GeneralNominalState (State Linked RootPending)
open GeneralSourceState (Demand)
open GeneralNominalCycleK2 (RecursAt RootK2)
open GeneralRebasePartialBool268 (Answer Reflect neg both either)
open GeneralRebasePartialFinite268 (any transfer any_sound)
open GeneralRebaseCandidateChecks267 (linked linked_exact allKnown allKnown_exact)
open GeneralRebasePartialCycles268 (Cycle Walk evaluate evaluate_sound evaluate_total)

theorem bool_reflect (p : Prop) (b : Bool) (corr : b = true ↔ p) : Reflect p (some b) := by
 cases b with
 | false => exact fun h => Bool.noConfusion (corr.mpr h)
 | true => exact corr.mp rfl

theorem mixed_walk (state : State) (first last : Fin state.base.slots) :
 Walk (GeneralNominalMixedRecurrence.Edge state) first last ↔ GeneralNominalMixedRecurrence.Path state first last := by
 constructor <;> intro path
 · induction path with
   | nil _ => exact .nil _
   | cons edge _ ih => exact .cons edge ih
 · induction path with
   | nil _ => exact .nil _
   | cons edge _ ih => exact .cons edge ih

theorem mixed_cycle (state : State) (root : Fin state.base.slots) :
 Cycle (GeneralNominalMixedRecurrence.Edge state) root ↔ GeneralNominalCycleK2.Cycle state root := by
 simp only [Cycle,GeneralNominalCycleK2.Cycle,GeneralNominalMixedRecurrence.Cycle,mixed_walk]

structure Probes (state : State) where
 edge : Fin state.base.slots → Fin state.base.slots → Answer
 model : Answer

structure Sound (state : State) (p : Probes state) : Prop where
 edge : ∀ a b, Reflect (GeneralNominalMixedRecurrence.Edge state a b) (p.edge a b)
 model : Reflect (∃ model, GeneralNominalState.Models state model) p.model

def evaluatedEdge (state : State) (p : Probes state) (a b : Fin state.base.slots) : Answer :=
 if b ∈ GeneralRebaseDirectCycles268.adj state a then some true else p.edge a b

theorem evaluatedEdge_sound (state : State) (p : Probes state) (sound : Sound state p)
 (a b : Fin state.base.slots) :
 Reflect (GeneralNominalMixedRecurrence.Edge state a b) (evaluatedEdge state p a b) := by
 unfold evaluatedEdge
 split
 · rename_i found
   exact GeneralNominalCycleK2.direct_edge_sound ((GeneralRebaseDirectCycles268.adj_exact ..).mp found)
 · exact sound.edge a b

def recurs (state : State) (p : Probes state) (slot : Fin state.base.slots) : Answer :=
 either (some (GeneralRebaseDirectCycles268.cycle state slot))
  (both (evaluate (evaluatedEdge state p) slot) p.model)

theorem recurs_sound (state : State) (p : Probes state) (sound : Sound state p) (slot : Fin state.base.slots) :
 Reflect (RecursAt state slot) (recurs state p slot) :=
 GeneralRebasePartialBool268.either_sound (bool_reflect _ _ (GeneralRebaseDirectCycles268.cycle_exact state slot))
   (GeneralRebasePartialBool268.both_sound
     (transfer (mixed_cycle state slot) (evaluate_sound _ _ (evaluatedEdge_sound state p sound) slot))
     sound.model)

def sourceRecurs (state : State) (p : Probes state) (id : Nat) : Answer :=
 any (fun slot => both (some (state.base.source slot == id)) (recurs state p slot)) (List.finRange state.base.slots)

theorem sourceRecurs_sound (state : State) (p : Probes state) (sound : Sound state p) (id : Nat) :
 Reflect (∃ slot, state.base.source slot = id ∧ RecursAt state slot) (sourceRecurs state p id) := by
 apply transfer (p := ∃ slot ∈ List.finRange state.base.slots, state.base.source slot = id ∧ RecursAt state slot)
 · simp
 · apply any_sound
   intro slot _
   exact GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (beq_iff_eq ..)) (recurs_sound state p sound slot)

def root (state : State) (p : Probes state) (demand : Demand roles) : Answer :=
 both (some (linked state demand))
  (both (some (allKnown state demand)) (any
   (fun index => sourceRecurs state p (demand.arguments index).1) (List.finRange (roles demand.role).arity)))

theorem root_sound (state : State) (p : Probes state) (sound : Sound state p) (demand : Demand roles) :
 Reflect (RootK2 state demand) (root state p demand) := by
 have found : Reflect (∃ index, ∃ slot, state.base.source slot = (demand.arguments index).1 ∧ RecursAt state slot)
   (any (fun index => sourceRecurs state p (demand.arguments index).1) (List.finRange (roles demand.role).arity)) := by
   apply transfer (p := ∃ index ∈ List.finRange (roles demand.role).arity,
     ∃ slot, state.base.source slot = (demand.arguments index).1 ∧ RecursAt state slot)
   · simp
   · exact any_sound _ _ _ (fun index _ => sourceRecurs_sound state p sound _)
 exact GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (linked_exact state demand))
   (GeneralRebasePartialBool268.both_sound (bool_reflect _ _ (allKnown_exact state demand)) found)

end Yulang.GeneralRebaseRawK2Probe268
