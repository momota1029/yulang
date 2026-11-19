import Yulang.GeneralRebaseDirectCycles268
import Yulang.GeneralRebaseDiagnosticSource268

namespace Yulang.GeneralRebaseDirectedRoot268
open GeneralSourceState (Demand)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalState (State Linked RootPending)
open GeneralRebaseDirectCycles268 (cycle cycle_exact)
open GeneralNominalCycleK2 (DirectCycle RootK2)
open GeneralRebaseCandidateChecks267 (linked linked_exact allKnown allKnown_exact)
open GeneralRebaseSourceSurvivor267 (Boundary)

def atSource (state : State) (id : Nat) : Bool :=
 (List.finRange state.base.slots).any fun slot => (state.base.source slot == id) && cycle state slot

theorem atSource_exact (state : State) (id : Nat) :
 atSource state id = true ↔ ∃ slot, state.base.source slot = id ∧ DirectCycle state slot := by
 simp only [atSource,List.any_eq_true,List.mem_finRange,true_and,Bool.and_eq_true,beq_iff_eq,cycle_exact]

def root (state : State) (demand : Demand roles) : Bool :=
 linked state demand && (allKnown state demand &&
 (List.finRange (roles demand.role).arity).any fun i => atSource state (demand.arguments i).1)

theorem root_exact (state : State) (demand : Demand roles) : root state demand = true ↔
 Linked state demand ∧ ¬ RootPending state demand ∧
 ∃ index slot, state.base.source slot = (demand.arguments index).1 ∧ DirectCycle state slot := by
 simp only [root,Bool.and_eq_true,linked_exact,allKnown_exact,List.any_eq_true,List.mem_finRange,true_and,atSource_exact]

theorem raw_sound (state : State) (demand : Demand roles) (trueCycle : root state demand = true) :
 RootK2 state demand := by
 obtain ⟨linked,known,i,slot,source,cycle⟩ := (root_exact ..).mp trueCycle
 exact ⟨linked,known,i,slot,source,Or.inl cycle⟩

/-- Zero is deliberately unknown for the actual root diagnostic, whose
semantic recurrence side is not covered by the finite direct graph. -/
def probe (state : GeneralNominalVersionedJournal232.State roles) (focus : Occurrence roles) : Option Bool :=
 if root state.core.erased.current.context.state (GeneralNominalVersionedCandidates231.inputs focus).demand then
   some true else none

theorem probe_sound (registry : GeneralDeclarations.Registry) (state : GeneralNominalVersionedJournal232.State roles)
 (focus : Occurrence roles) :
 GeneralRebasePartialBool268.Reflect ((Boundary roles).RootK2 registry state focus) (probe state focus) := by
 unfold probe
 split
 · rename_i positive
   exact Or.inl (raw_sound _ _ positive)
 · trivial

theorem negative_incomplete (state : State) (demand : Demand roles)
 (noDirect : root state demand = false) (actual : RootK2 state demand) :
 ∃ index slot, state.base.source slot = (demand.arguments index).1 ∧
 (GeneralNominalCycleK2.Cycle state slot ∧ ∃ model, GeneralNominalState.Models state model) := by
 obtain ⟨linked,known,i,slot,source,cycles⟩ := actual
 refine ⟨i,slot,source,?_⟩
 rcases cycles with direct | semantic
 · have contradiction := (root_exact ..).mpr ⟨linked,known,i,slot,source,direct⟩
   simp [noDirect] at contradiction
 · exact semantic

end Yulang.GeneralRebaseDirectedRoot268
