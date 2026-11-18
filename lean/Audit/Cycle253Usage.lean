import Yulang.GeneralDictionaryCompoundPoolRepair253
import Yulang.GeneralDictionaryOutputDepthRepair253
import Yulang.GeneralNominalRawFinite253
import Yulang.GeneralPatternDependencyDepth253
import Yulang.GeneralDeclarationOutputDepth253
import Yulang.GeneralNominalPublicBasis253
import Yulang.GeneralNominalAllHeadReadback253
namespace Cycle253Usage
open Yulang
open GeneralDeclarationPatterns GeneralPatternAdditiveDepth253
open Core.PresenceGeneration (TyTerm)

example : depth ((tower 2 (.var 0)).subst (fun _ => tower 1 (.app 2 []))) = 4 := rfl
example : depth ((tower 2 (.var 0)).subst (fun _ => .var 700)) = 2 := rfl
example : GeneralNominalExprDepth253.rawDepth (.nominal 0 [.nominal 0 [.variable 0]]) = 2 := rfl
example : (GeneralNominalRawFinite253.choices [.var 0,.var 1]
 (.join (.variable 0) (.nominal 1 [.variable 0,.variable 1]))).length = 8 := rfl
example : (GeneralNominalRawFinite253.choices [] (.nominal 2 [])).length = 1 := rfl
example : (GeneralNominalRawFinite253.choices [] (.variable 0)).length = 0 := rfl

example : (GeneralNominalPublicPorts253.ports GeneralDictionaryJournalRefinement228Source.snapshot.seed
 GeneralDictionaryJournalRefinement228Source.root.identity GeneralDictionaryCompoundSource238.declaration).length = 2 := rfl
example : GeneralDictionaryCompoundPool253.endpoint ∉
 GeneralNominalState.sources GeneralDictionaryJournalRefinement228Source.snapshot :=
 GeneralDictionaryCompoundPool253.endpoint_new
example (keys : List (Nat × Nat)) : GeneralDictionaryCompoundPool253.endpoint ∉
 GeneralNominalOutputNames253.outputs GeneralDictionaryCompoundSource238.registry
 GeneralDictionaryJournalRefinement228Source.snapshot.seed keys := by
 rw [GeneralDictionaryCompoundPool253.no_named_outputs]
 simp
example : GeneralDictionaryCompoundPool253.endpoint ∈
 GeneralNominalPublicPorts253.ports GeneralDictionaryJournalRefinement228Source.snapshot.seed
 GeneralDictionaryJournalRefinement228Source.root.identity GeneralDictionaryCompoundSource238.declaration :=
 GeneralDictionaryCompoundPoolRepair253.endpoint_in_ports

example : GeneralDictionaryOutputDepthRepair253.newDepth GeneralDictionaryOutputDepth252.expanded =
 GeneralDictionaryOutputDepthRepair253.newDepth GeneralDictionaryOutputDepth252.template +
 GeneralDictionaryOutputDepthRepair253.newDepth GeneralDictionaryOutputDepth252.rootPattern :=
 GeneralDictionaryOutputDepthRepair253.sharp
example : WellFounded (GeneralDeclarationProducerRank253.Child GeneralDeclarationExamples.constructors GeneralDeclarationExamples.roles) :=
 GeneralDeclarationProducerRank253.calls_wellFounded _ _

example (source : GeneralNominalSourceFormation.InitialSource registry context (root : GeneralSourceDictionaries.Occurrence roles))
 (keys : List (Nat × Nat)) (invocation declaration binder : Nat) :
 GeneralNominalPublicBasis253.privateName context.state.seed invocation declaration 0 binder 0 ∉
 GeneralPresenceSubstitutionSupport244.typeSources
 (GeneralPresenceUnionNormal252.normalize (GeneralNominalPublicBasis253.basis registry context keys) (.var 42)) :=
 GeneralNominalPublicBasis253.lower_private_free source keys _ invocation declaration 0 binder 0 (by decide)
example (source : GeneralNominalSourceFormation.InitialSource registry context (root : GeneralSourceDictionaries.Occurrence roles))
 (keys : List (Nat × Nat)) (invocation declaration binder position : Nat) :
 GeneralNominalPublicBasis253.privateName context.state.seed invocation declaration 1 binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources
 (GeneralPresenceInterNormal252.normalize (GeneralNominalPublicBasis253.basis registry context keys) (.var 42)) :=
 GeneralNominalPublicBasis253.upper_private_free source keys _ invocation declaration 1 binder position (by decide)
example : WellFounded (GeneralDeclarationProducerRank253.NormalizedChild GeneralDeclarationExamples.constructors GeneralDeclarationExamples.roles) :=
 GeneralDeclarationProducerRank253.normalized_calls_wellFounded _ _
example : GeneralDeclarationPatterns.coveredArgs (GeneralDeclarationPatterns.normalizeArgs GeneralDictionaryOutputDepth252.declaration.head) = true := rfl
example (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key GeneralDictionaryOutputDepth252.plan)
 (branch : GeneralNominalVersionedPlans231.Holds GeneralDictionaryOutputDepth252.plan assignment)
 (known : GeneralNominalCenteredHeadMatSemanticLabels.Inputs
   (GeneralNominalCenteredHeadMatCompilerSemantics.algebra GeneralDictionaryOutputDepth252.plan.packet.registry.constructors
     GeneralDictionaryOutputDepth252.plan.packet.context.interpretation)
   assignment GeneralDictionaryOutputDepth252.plan.input labels) :
 ∃ capture : Nat → Pattern, ∀ name ∈ GeneralDictionaryOutputDepth252.plan.packet.declaration.inputNames,
 depth (capture name) ≤ GeneralNominalPatersonLineage.mass labels := by
 obtain ⟨capture,_,_,bounds,_⟩ := GeneralNominalAllHeadReadback253.readback_depth_covered frame (by rfl) branch known
 exact ⟨capture,bounds⟩
end Cycle253Usage
