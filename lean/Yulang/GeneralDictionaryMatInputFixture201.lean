import Yulang.GeneralDictionaryMatInputAssembly201
import Yulang.GeneralNominalCenteredPointMergeExample

namespace Yulang.GeneralDictionaryMatInputFixture201
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryEarlyMergeExample (registry declaration packet checked)
open GeneralNominalCenteredPointMergeExample (plan)
open GeneralNominalExamples (context state displayRoot model state_models)
open GeneralDictionaryMatInputVariables201

/-- Two genuine required clauses, each forwarding the same input variable. -/
theorem restricted : InputVariableClauses declaration := by
  intro clause member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · simp [Declaration.inputNames,Declaration.outputNames,variablesArgs,Pattern.variables,normalizeArgs,normalize]
  · simp [Declaration.inputNames,Declaration.outputNames,variablesArgs,Pattern.variables,normalizeArgs,normalize]

theorem head_models (assignment : Assignment) (valid : GeneralNominalState.Models (state true) assignment) :
    GeneralNominalCenteredHeadCandidates.HeadModels registry (context true) displayRoot declaration [(0,0)] assignment := by
  have branch := GeneralDictionaryEarlyMergeExample.branch assignment valid
  exact ⟨branch.1,branch.2.1⟩

theorem head_equations (assignment : Assignment) (valid : GeneralNominalState.Models (state true) assignment) :
    GeneralNominalCenteredHeadOutputs.HeadEquations plan assignment := by
  have equations := GeneralNominalCenteredPointMergeExample.equations assignment valid
  exact ⟨equations.1,fun name present => equations.2.1 name (Or.inl present),equations.2.2.1⟩

abbrev start := GeneralNominalCenteredHeadMatStepJournal.initial (context true) displayRoot

theorem class_effects (assignment : Assignment) :
    GeneralNominalCenteredHeadMatEffects.ClassEffects start.core displayRoot plan assignment := by
  have empty : GeneralNominalCenteredHeadOutputs.requests start.core displayRoot = [] := by
    unfold GeneralNominalCenteredHeadOutputs.requests
    apply List.flatMap_eq_nil_iff.mpr
    intro site member
    have registered := (List.mem_filter.mp member).1
    have same : site = plan.input.observed := List.mem_singleton.mp registered
    subst site
    rfl
  constructor
  · intro output member; rw [empty] at member; cases member
  · intro a member; rw [empty] at member; cases member

theorem total_holds (assignment : Assignment) (valid : GeneralNominalState.Models (state true) assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment :=
  GeneralDictionaryMatInputAssembly201.holds_of_head_class plan start.core
    (List.mem_singleton_self _) assignment (head_models assignment valid)
    (head_equations assignment valid) (class_effects assignment) restricted

theorem journal_models : GeneralNominalCenteredHeadMatStepJournal.Models start model :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl)).mpr (state_models true)

theorem child_count : plan.packet.children.length = 2 := by
  simp [GeneralNominalSaturationState.Packet.children,GeneralNominalAllocation.children,
    GeneralDictionaryEmissionPlans.children,GeneralCanonicalChildOrder.canonicalEmit,
    GeneralDeclarationDemands.emitAll,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,packet,declaration,List.mergeSort_pair]

theorem checked_nonterminal_total :
    DeclarationChecked registry.constructors GeneralDeclarationExamples.roles declaration ∧
    declaration.requirements.length = 2 ∧
    GeneralNominalState.Models (state true) model ∧
    GeneralNominalCenteredHeadMatStepPackets.Holds plan model :=
  ⟨checked,rfl,state_models true,total_holds model (state_models true)⟩

end Yulang.GeneralDictionaryMatInputFixture201
