import Yulang.GeneralNominalCenteredHeadMatCompletionCollisionLocal

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatCompletionCollisionPackets
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatExpressions CommonNominalFullCarrier
open GeneralNominalCenteredHeadMatCompletionCollisionSource
open GeneralNominalCenteredHeadMatCompletionCollisionLocal

abbrev target := GeneralNominalAllocation.source snapshot registry root.identity
  (GeneralNominalAllocation.origin root.identity declaration.id 5 43 0)

theorem different_clauses : firstClause.id ≠ lastClause.id := by decide +kernel

theorem same_target :
    (GeneralNominalAllocation.allocation (roles := roles) snapshot registry root.identity declaration.id firstClause).outputs 43 =
      (GeneralNominalAllocation.allocation (roles := roles) snapshot registry root.identity declaration.id lastClause).outputs 43 := rfl

theorem canonical_declaration : GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration := by
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_pair]

theorem int_translation : translate GeneralDeclarationExamples.constructors GeneralNominalExamples.interpretation (.app 2 []) =
    some (.primitive (.scalar .int) []) := rfl

theorem variant_translation : translate GeneralDeclarationExamples.constructors GeneralNominalExamples.interpretation (.variant 0 (.app 2 [])) =
    some (.variant 0 (.primitive (.scalar .int) [])) := rfl

theorem schema_exact : GeneralNominalCenteredHeadMatPlans.emittedSchema plan =
    ⟨[⟨target,.actual,.primitive (.scalar .int) []⟩,
      ⟨target,.actual,.variant 0 (.primitive (.scalar .int) [])⟩],false⟩ := by
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,canonical_declaration]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalCenteredHeadMatSchemas.emissionRequests,List.ofFn_zero,
    GeneralNominalCenteredHeadMatSchemas.generated,GeneralNominalCenteredHeadMatSchemas.materialize,
    GeneralNominalCenteredHeadMatSchemas.Schema.append,int_translation,variant_translation,
    GeneralDeclarationDemands.outputTarget,normalize,normalizeArgs,GeneralNominalAllocation.allocation,target,
    GeneralNominalDemandMerging.pointSite]

theorem materialized : (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).unknown = false := by
  rw [schema_exact]

theorem int_not_variant : ¬ Equivalent (.base .int) (variant 0 (.base .int)) := by
  intro equal
  have impossible := GeneralNominalFiniteHeadInversion.equivalent_head (.scalar .int) (.structural (.variant 0))
    Fin.elim0 (fun _ => .base .int) equal
  cases impossible

theorem no_packet_model (assignment : GeneralNominalCommonBridge.Assignment) :
    ¬ GeneralNominalCenteredHeadMatStepPackets.Holds plan assignment := by
  intro valid
  have outputs := valid.2.2
  unfold GeneralNominalCenteredHeadMatStepPackets.Outputs at outputs
  rw [schema_exact] at outputs
  have first := outputs ⟨target,.actual,.primitive (.scalar .int) []⟩ (by simp)
  have last := outputs ⟨target,.actual,.variant 0 (.primitive (.scalar .int) [])⟩ (by simp)
  exact int_not_variant ⟨subtype_trans first.2 last.1,subtype_trans last.2 first.1⟩

theorem no_common_model : ¬ ∃ assignment,
    GeneralNominalCenteredHeadMatStepJournal.Models start assignment ∧
      GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan assignment ∧ effect.Holds assignment := by
  rintro ⟨assignment,_,packet,_⟩
  exact no_packet_model assignment packet

theorem not_packetAssembly : ¬ GeneralNominalCenteredHeadMatCompletionAssembly.PacketAssembly roles := by
  intro assembly
  exact no_common_model (assembly registry ⟨rfl,checked⟩ start root effect reachable rfl rfl ⟨model,effect_model⟩)

end Yulang.GeneralNominalCenteredHeadMatCompletionCollisionPackets
