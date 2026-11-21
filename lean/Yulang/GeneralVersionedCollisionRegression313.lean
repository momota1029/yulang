import Yulang.GeneralVersionedCollisionSource313
import Yulang.GeneralVersionedCompiledFirstInstall313

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! Real source regression: two clauses with the same local computed output
ID have distinct compiled targets, and the first mixed installation exists.
This is not the hypothetical unclipped raw-compiler collision. -/
namespace Yulang.GeneralVersionedCollisionRegression313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryJournalRefinement228Source
open GeneralVersionedCollisionSource313
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local local_iff)
open GeneralNominalVersionedDiagnostic232 (HeadEquations)
open GeneralDictionaryCompoundVersionedModel238 (extended)
open GeneralVersionedComputedRows313 (output_target)
open GeneralVersionedCompoundRows313 (address)
open GeneralNominalVersionedFrame231 (capture frame)

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry before root := by
  refine ⟨GeneralDictionaryCompoundPacket238.known,?_,?_,?_⟩
  · rintro (raw | (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs slot cycle
    · exact GeneralDictionaryCompoundStep238.acyclic _ cycle
    · exact GeneralDictionaryCompoundStep238.acyclic _ cycle
  · rintro (raw | ⟨candidate,framed,entry,_,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralDictionaryOptionalEnable229.no_raw_recurs visited.1 cycle
    · exact GeneralDictionaryCompoundStep238.acyclic _ cycle
  · rintro (⟨_,other,visible,_,_,unprepared⟩ | unready)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · exact unready GeneralDictionaryCompoundStep238.administrative_ready

theorem model : Models before extended := GeneralDictionaryCompoundVersionedModel238.initial_model

theorem head : HeadEquations plan extended :=
  GeneralVersionedSelectedJointHead312.head_of_schema GeneralVersionedCollisionSource313.frame model private_head
    GeneralDictionaryCompoundVersionedPacket238.head_holds

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready before.core root plan :=
  GeneralNominalVersionedMixedReady235.ready boundary_checked reachable GeneralVersionedCollisionSource313.frame

theorem class_done : GeneralNominalVersionedEffects231.ClassEffects before.core root plan extended :=
  GeneralDictionaryCompoundFrame238.class_effects

theorem sharing_clear : ¬ GeneralNominalVersionedDiagnostic232.SharingConflict registry before root := by
  rintro ⟨other,kids,other_unique,_,_,_,wrong⟩
  have same : d.id = other := (other_unique.2 _ _ survivor).1
  subst other
  apply wrong
  exact ⟨extended,model,plan,GeneralVersionedCollisionSource313.frame,
    GeneralNominalVersionedHeadSharing232.schema_holds plan extended head.2.2⟩

theorem merged_clear : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict before root := by
  rintro ⟨⟨first,last,member,_,_⟩,_⟩
  cases member

theorem output_clear : ¬ GeneralNominalVersionedDiagnostic232.OutputConflict registry before root d.id := by
  rintro ⟨_,impossible⟩
  exact impossible ⟨extended,model,⟨_,unique⟩,plan,GeneralVersionedCollisionSource313.frame,ready,head,class_done⟩

theorem selected : Local sourceRegistry before root (.selected d.id (GeneralNominalVersionedFrame231.children packet)) := by
  apply local_iff.mpr
  exact .ordinary sharing_clear (.ordinary merged_clear (.selected safe unique output_clear))

noncomputable def effect : Effect roles where
  registry := registry
  snapshot := before.core
  plan := plan
  frame := GeneralVersionedCollisionSource313.frame
  unique := unique
  ready := ready

theorem enabled : GeneralNominalVersionedMixedKernel234.Installable registry before effect :=
  GeneralVersionedCompiledFirstInstall313.installable boundary_checked reachable rfl selected rfl rfl ⟨_,model⟩

theorem keys_distinct : (GeneralNominalCenteredHeadAllocEncoding.equation left.id width).id ≠
    (GeneralNominalCenteredHeadAllocEncoding.equation right.id GeneralVersionedCollisionSource313.exact).id := by
  intro same
  have e := (GeneralNominalCenteredHeadAllocEncoding.equation_key.mp same).1
  cases e

theorem target_distinct :
    address plan 5 (GeneralNominalCenteredHeadAllocEncoding.equation left.id width).id 0 ≠
    address plan 5 (GeneralNominalCenteredHeadAllocEncoding.equation right.id GeneralVersionedCollisionSource313.exact).id 0 := by
  intro equal
  have fields := (GeneralNominalIdentities.source_identity snapshot.seed _ _).mp equal
  exact keys_distinct (congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.2.1) fields)


abbrev leftClause := GeneralNominalCenteredHeadAllocEncoding.clause left
abbrev rightClause := GeneralNominalCenteredHeadAllocEncoding.clause right
abbrev leftOutput := GeneralNominalCenteredHeadAllocEncoding.equation left.id width
abbrev rightOutput := GeneralNominalCenteredHeadAllocEncoding.equation right.id GeneralVersionedCollisionSource313.exact
abbrev outputLeft := address plan 5 leftOutput.id 0
abbrev outputRight := address plan 5 rightOutput.id 0
abbrev leftRow : GeneralNominalCenteredHeadMatSchemas.Equation := ⟨outputLeft,.actual,.primitive .emptyRecord []⟩
abbrev rightRow : GeneralNominalCenteredHeadMatSchemas.Equation := ⟨outputRight,.actual,.primitive .exactEmpty []⟩

theorem left_row : GeneralVersionedComputedRows313.OutputCell plan leftRow := by
  refine ⟨leftClause,List.mem_cons_self,leftOutput,List.mem_singleton_self _,?_,rfl,rfl,rfl⟩
  rintro ⟨name,norm,member⟩
  cases norm

theorem right_row : GeneralVersionedComputedRows313.OutputCell plan rightRow := by
  refine ⟨rightClause,List.mem_cons_of_mem _ (List.mem_singleton_self _),rightOutput,List.mem_singleton_self _,?_,rfl,rfl,rfl⟩
  rintro ⟨name,norm,member⟩
  cases norm

theorem not_committed : ¬ GeneralNominalVersionedInstallStep232.Committed before plan := by
  intro committed
  have hasChild : GeneralNominalVersionedFrame231.children packet ≠ [] := by
    intro empty
    have length := List.length_eq_zero_iff.mpr empty
    have actual := (GeneralNominalVersionedChildren232.emitted_length plan)
    rw [← GeneralNominalVersionedChildren232.emitted_occurrences plan,List.length_map] at length
    rw [length] at actual
    cases actual
  obtain ⟨child,present⟩ := List.exists_mem_of_ne_nil _ hasChild
  have impossible := committed.2 child present
  cases impossible

noncomputable abbrev after := GeneralNominalVersionedInstall232.install before effect

theorem step : GeneralNominalVersionedMixedKernel234.Step registry root before after :=
  ⟨root,.root,.install effect enabled not_committed⟩

theorem recorded : GeneralNominalVersionedTraceSupport237.Reachable sourceRegistry root after :=
  ⟨before,initial,.tail .refl step⟩

theorem two_outputs_same_model :
    ∃ m, Models after m ∧ CommonNominalFullCarrier.Equivalent (m outputLeft).1 .emptyRecord ∧
      CommonNominalFullCarrier.Equivalent (m outputRight).1 CommonNominalFullCarrier.exactEmpty := by
  obtain ⟨m,witness⟩ := enabled.common
  have branch := witness.2.1
  have one := GeneralNominalVersionedPlans231.emitted_equation (plan := plan) branch.2.2
    (GeneralVersionedComputedRows313.row_present left_row)
  have two := GeneralNominalVersionedPlans231.emitted_equation (plan := plan) branch.2.2
    (GeneralVersionedComputedRows313.row_present right_row)
  exact ⟨m,(GeneralNominalVersionedInstall232.install_models rfl).mpr witness,one,two⟩

end Yulang.GeneralVersionedCollisionRegression313
