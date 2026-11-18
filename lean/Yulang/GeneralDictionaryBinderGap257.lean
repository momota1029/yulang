import Yulang.GeneralDictionaryReportProjection257
import Yulang.GeneralDictionaryLooseIterationPatched240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryBinderGap257
open Core.PresenceGeneration
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralDictionaryLooseLoopSource240 (roles model initial F S)
open GeneralDictionaryLooseLoopPacket240 (actual)
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseIterationBook240 (context plan)
open GeneralDictionaryUpperHistory257 (history)
open GeneralPresenceOrderedBlock247 (solve)

noncomputable def seed : Assignment :=
 fun name => if name = actual then (.bottom,(model name).2) else model name
noncomputable def witness (n : Nat) : Assignment := solve CommonNominalFullCarrier.model (history n) seed

theorem actual_above : 4 < actual := GeneralNominalIdentities.source_above_seed ..

theorem seed_initial (name : Nat) (small : name ≤ 4) : seed name = model name := by
 have different : name ≠ actual := by have above := actual_above; omega
 simp only [seed,different,ite_false]

theorem seed_models : GeneralNominalVersionedJournal232.Models initial seed := by
 apply (GeneralNominalVersionedJournalFrame236.models_iff initial ?_).mp GeneralDictionaryLooseLoopSource240.initial_model
 intro name member
 have initial := GeneralDictionaryLooseIterationPatched240.initial_support member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at initial
 exact (seed_initial name (by omega)).symm

theorem raw_witness (n : Nat) : GeneralNominalState.Models (context n).state (witness n) := by
 have raw0 : GeneralNominalState.Models (context 0).state seed := by
   rw [GeneralDictionaryLooseIterationBook240.context_zero]
   exact ((GeneralNominalVersionedJournal232.initial_models ..).mp seed_models).1
 have compact0 := (GeneralDictionaryCompactView257.recovered 0 seed (by intro atom member; cases member)).mpr raw0
 have small0 := (GeneralDictionaryFiveSlot257.models_exact 0 seed).mp compact0
 have small := (GeneralDictionaryNoModelRefinement257.all_iff_zero n seed).mpr small0
 exact (GeneralDictionaryCompactView257.compact_solved n seed).mp
   ((GeneralDictionaryFiveSlot257.models_exact n seed).mpr small)

theorem actual_outside (n : Nat) (entry : GeneralPresenceDefinitionRewrite244.Entry Nat)
 (member : entry ∈ history n) : entry.1 ≠ actual := by
 induction n with
 | zero => cases member
 | succ n ih =>
   rcases List.mem_append.mp member with old | fresh
   · exact ih old
   · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh
     rcases fresh with rfl | rfl
     · exact GeneralNominalAggregateVersion231.not_legacy_slot 4 0 0 0 0 _ 0 0 8 0
     · exact GeneralNominalAggregateVersion231.not_legacy_slot 4 0 0 1 0 _ 0 0 8 0

theorem actual_bottom (n : Nat) : (witness n actual).1 = .bottom := by
 have same := GeneralPresenceOrderedBlock247.solve_outside CommonNominalFullCarrier.model (history n) seed actual (actual_outside n)
 change (solve CommonNominalFullCarrier.model (history n) seed actual).1 = _
 rw [same]
 simp only [seed,ite_true]

theorem lower_value (n index : Nat) (before : index ≤ n) :
 Equivalent (witness n (lower index)).1 F := by
 have evaluation := GeneralPresenceOrderedSubstitution247.mapping_eval (history n) CommonNominalFullCarrier.model seed (lower index)
 have normal := GeneralPresenceIdempotentTree257.equivalent
   (GeneralPresenceOrderedSubstitution247.mapping (history n) (lower index)).ty seed
 rw [GeneralDictionaryFullReduced257.lower_fixed n index before] at normal
 change Equivalent (seed 2).1 _ at normal
 rw [seed_initial 2 (by decide)] at normal
 have equal := congrArg Prod.fst evaluation
 change (GeneralPresenceOrderedSubstitution247.mapping (history n) (lower index)).ty.eval CommonNominalFullCarrier.model seed = (witness n (lower index)).1 at equal
 change Equivalent F ((GeneralPresenceOrderedSubstitution247.mapping (history n) (lower index)).ty.eval CommonNominalFullCarrier.model seed) at normal
 rw [equal] at normal
 exact ⟨normal.2,normal.1⟩
theorem not_inputs (n index : Nat) (before : index < n) :
 ¬ GeneralNominalVersionedPlans231.Inputs (plan index) (witness n) := by
 intro input
 have fits := GeneralNominalVersionedPlans231.shared_center input (name := 0)
   (Or.inl (by change 0 ∈ GeneralDictionaryLooseLoopSource240.declaration.inputNames; decide +kernel))
 rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryLooseFamilyFull240.binder_exact] at fits
 change GeneralNominalCaptureMerges.Fits (witness n)
   ((GeneralNominalVersionedAllocation231.capture _ _ _ _ (GeneralDictionaryLooseIterationBook240.packet index).bindings).inputs 0)
   (witness n actual).1 at fits
 rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact] at fits
 change Subtype (witness n (lower (index+1))).1 (witness n actual).1 ∧
   Subtype (witness n actual).1 (witness n (upper index)).1 at fits
 rw [actual_bottom] at fits
 have impossible := subtype_trans (lower_value n (index+1) (by omega)).2 fits.1
 exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
   ⟨[.inl S],rfl,(by
     intro depth
     apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
     intro rank env observation accepted
     exact CommonNominalFullDemand.probeAt_bottom rank observation),impossible⟩

theorem not_journal (n : Nat) :
 ¬ GeneralNominalVersionedJournal232.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)) (witness (n+1)) := by
 intro valid
 have held := valid.2.1 (plan 0) ((GeneralDictionaryLooseIterationIteration240.stages (n+1)).recorded 0 (by omega))
 exact not_inputs (n+1) 0 (by omega) held.2.1

/-- Actual current raw Models cannot replace a recorded journal certificate.
The witness changes a fixed purpose8 binder that the raw View does not read. -/
theorem current_raw_not_journal (n : Nat) :
 GeneralNominalState.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)).core.erased.current.context.state (witness (n+1)) ∧
 ¬ GeneralNominalVersionedJournal232.Models
   (GeneralDictionaryLooseIterationIteration240.state (n+1)) (witness (n+1)) := by
 constructor
 · rw [(GeneralDictionaryLooseIterationIteration240.stages (n+1)).shape.current]
   exact raw_witness (n+1)
 · exact not_journal n
end Yulang.GeneralDictionaryBinderGap257
