import Yulang.GeneralDeclarativeWitnessWholeFixture361

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 68000
set_option maxHeartbeats 74000000
namespace Yulang.GeneralDeclarativeWitnessWholeSound361
open GeneralDeclarativeWitnessWholeFixture361 (Done process passes actual_ordinary_before_authority_and_native_after)
open GeneralDeclarativeWitnessMixedForwardSound361 (ordered_dictionary_sound)
open GeneralDeclarativeWitnessAuthorOrdinaryChoice361 (alias_read_witness)
open GeneralDeclarativeWitnessNativeInstall360 (Fits NativeViews interpreted)
open GeneralDeclarativeWitnessNativeSnapshot360 (same_exact current_target_keeps_others)
open GeneralDeclarativeWitnessNativePreparation360 (same_model_of_prepared)
open GeneralDeclarativeWitnessNestedModel361 (state model model_fits)
open GeneralDeclarativeWitnessNestedInstall360 (requested layout)
open GeneralDeclarativeWitnessReleasedForward360 (forwardDemand knownTarget)
open GeneralDeclarativeWitnessJointObservation359 (firstLo firstHi)
open GeneralDeclarativeWitnessSourceEndpoint359 (endpoint_in_model)
open GeneralDeclarativeWitnessOpenSpine359 (sem)
open GeneralDeclarativeWitnessLiteral349 (preserves_iff)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonRoleOutermostResolver (Frontier Classify)

inductive BodyLocal {negative : Bool} (f : Done negative) : Demand → Frontier Demand → Prop where
  | writer : BodyLocal f requested (.selected f.writer.root.prep.impl.id [f.ordinary.asked])
  | whereChild : BodyLocal f f.ordinary.asked (.selected f.ordinary.prepared.impl.id [])

theorem author_tree {negative} (f : Done negative) :
    Classify (BodyLocal f) requested
      (.selected (.node f.writer.root.prep.impl.id [.node f.ordinary.prepared.impl.id []])) := by
  refine ⟨.selected f.writer.root.prep.impl.id [.selected f.ordinary.prepared.impl.id []],?_,?_⟩
  · exact .selected .writer (.cons (.selected .whereChild .nil) .nil)
  · exact .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)

theorem same_model_of_ordered_source {negative} (f : Done negative) (m : Assignment) (v : NativeViews)
    (fit : Fits f.native.leaf.result.world m v) :
    Classify (BodyLocal f) requested (.selected (.node f.writer.root.prep.impl.id [.node f.ordinary.prepared.impl.id []])) ∧
    Classify (GeneralDeclarativeWitnessMixedForwardSound361.Local f.native) forwardDemand
      (.selected (.node f.native.parent.impl.id [.node f.native.leaf.chosen.impl.id []])) ∧
    Equivalent (m 106).1 (sem m (firstLo.code 60)) ∧
    Equivalent (m 107).1 (sem m (firstHi.code 62)) ∧
    v knownTarget.center = some (f.writer.root.typed.write.code.eval m) ∧
    GeneralDeclarativeHead320.Models layout.named m ∧
    f.writer.root.prep.kids = [f.ordinary.asked] ∧
    f.forward.actual.continuation.kids = [f.forward.actual.receiver] := by
  have afterForward := restrict ((preserves_iff ..).mp f.native.leaf.result.kept) m fit.1
  have afterBody := (same_model_of_prepared f.forward.actual.continuation m afterForward).1
  change GeneralDeclarativeHead320.Models f.forward.actual.ordinaryChild.result.state m at afterBody
  rw [f.forward.sameBody] at afterBody
  have beforeBody := restrict ((preserves_iff ..).mp f.ordinary.keeps) m afterBody
  have beforeWrite : Fits f.writer.root.final m v := ⟨beforeBody,fit.2⟩
  have src := f.ordinary.found.authored
  have arrival := ordered_dictionary_sound f.native m v fit
  have initial := current_target_keeps_others f.writer.root.prep f.writer.root.typed f.writer.root.wrote m v beforeWrite
  refine ⟨author_tree f,arrival.1,?_,?_,arrival.2.2.2.2.1,initial.1,f.ordinary.exactChild,arrival.2.2.1⟩
  · exact eqv_trans (alias_read_witness f.ordinary.found.originLo m beforeBody) (endpoint_in_model src.lower m beforeBody)
  · exact eqv_trans (alias_read_witness f.ordinary.found.originHi m beforeBody) (endpoint_in_model src.upper m beforeBody)

theorem reconstructed_author_and_forwarder_share_one_state (negative : Bool) :
    ∃ f : Done negative,
      process negative = some f ∧
      Classify (BodyLocal f) requested (.selected (.node 72 [.node 73 []])) ∧
      Classify (GeneralDeclarativeWitnessMixedForwardSound361.Local f.native) forwardDemand
        (.selected (.node 74 [.node 75 []])) ∧
      f.ordinary.result.fixed = [⟨105,.variable 61⟩] ∧
      (∀ upper scalar,Fits f.native.leaf.result.world (model upper scalar)
        (interpreted f.native.leaf.result.world.board (model upper scalar))) ∧
      ∀ m v,Fits f.native.leaf.result.world m v →
        Holds m ⟨105,.variable 61⟩ ∧ v knownTarget.center = some (f.writer.root.typed.write.code.eval m) := by
  have gate := actual_ordinary_before_authority_and_native_after negative
  cases runs : process negative with
  | none => rw [runs] at gate; cases gate
  | some f =>
    rw [runs] at gate
    have both := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp (show passes f = true from gate)).1
    have first := of_decide_eq_true both.1
    have second := Bool.and_eq_true_iff.mp both.2
    have ids := of_decide_eq_true (Bool.and_eq_true_iff.mp second.1).1
    have actual := same_exact.mp second.2
    have fit (u : Bool) (b : Inference.Base) :
        Fits f.native.leaf.result.world (model u b) (interpreted f.native.leaf.result.world.board (model u b)) :=
      ⟨actual.symm ▸ model_fits u b,fun _ => rfl⟩
    have evidence := same_model_of_ordered_source f _ _ (fit false .int)
    refine ⟨f,rfl,?_,?_,first.2.2,fit,?_⟩
    · rw [← first.1,← first.2.1]; exact evidence.1
    · rw [← ids.1,← ids.2]; exact evidence.2.1
    · intro m v fitting
      have same := same_model_of_ordered_source f m v fitting
      refine ⟨?_,same.2.2.2.2.1⟩
      have ordinary := fitting.1.2
      rw [actual] at ordinary
      exact ordinary _ (List.mem_append_right _ (by decide +kernel))

end Yulang.GeneralDeclarativeWitnessWholeSound361
