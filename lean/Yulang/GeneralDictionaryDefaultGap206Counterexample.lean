import Yulang.GeneralDictionaryDefaultGap206State
import Yulang.GeneralDictionaryTotalBoundary206

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultGap206Counterexample
open GeneralDictionaryDefaultGap206Source GeneralDictionaryDefaultGap206Local
open GeneralDictionaryDefaultGap206State
open GeneralDictionaryTotalEvidence206
open GeneralDictionaryAssociatedProvenance

theorem no_default_output : ¬ GeneralDictionaryDefaultEvidence204.OutputWitness plan counter ⟨0,0⟩ := by
  rintro ⟨body,supplied,_,holds⟩
  have found := (lookup_exact roles declaration declaration_checked.identified.2.2.1 0 body).mpr supplied
  have same : body = .default 0 0 (.var 0) := Option.some.inj found.symm
  subst body
  have equal := (GeneralNominalCenteredHeadMatEffects.positional_default plan counter (0 : Fin 1)).mp holds
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.scalar .int) equal

theorem no_instance (kids) : ¬ Instance registry start.core counter root 37 kids := by
  rintro ⟨candidate,certificate⟩
  cases frame_plan certificate.frame
  exact no_default_output (certificate.outputs ⟨0,0⟩ (List.mem_singleton_self _))

theorem no_evidence : ¬ Evidence registry start.core counter root (.node 37 []) := by
  intro evidence
  have payload := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
  cases payload with
  | node source children => exact no_instance _ source

theorem not_evidenceNode : ¬ B4SkeletonV7.EvidenceNode (GeneralDictionaryTotalBoundary206.boundary roles) := by
  intro node
  apply no_evidence
  exact node registry ⟨rfl,checked⟩ start root alloc_reachable counter counter_inhabited root 37 [] []
    (Or.inl rfl) stable (by intro child member; cases member)
    (GeneralDictionaryTotalBoundary206.local_iff.mpr v7_selected) .nil

theorem positive_premises :
    (GeneralDictionaryTotalBoundary206.boundary roles).Checked registry ∧
    (GeneralDictionaryTotalBoundary206.boundary roles).Initial registry root start ∧
    B4TargetV7.Reachable (GeneralDictionaryTotalBoundary206.boundary roles) registry root start ∧
    (GeneralDictionaryTotalBoundary206.boundary roles).Models start counter ∧
    (GeneralDictionaryTotalBoundary206.boundary roles).Stable registry start root ∧
    B4TargetV7.Local (GeneralDictionaryTotalBoundary206.boundary roles) registry start root (.selected 37 []) ∧
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => (GeneralDictionaryTotalBoundary206.boundary roles).Evidence registry start counter child dictionary)
      [] [] :=
  ⟨⟨rfl,checked⟩,alloc_initial,alloc_reachable,counter_inhabited,stable,
    GeneralDictionaryTotalBoundary206.local_iff.mpr v7_selected,.nil⟩

/-- The operational commitment omits the default equation, which fails in a
real source model although a different source model satisfies all class effects. -/
theorem committed_without_default :
    GeneralNominalCenteredHeadMatStepKernel.Committed start plan ∧
    GeneralNominalCenteredHeadMatStepPackets.Holds plan counter ∧
    GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan model ∧
    ¬ GeneralDictionaryDefaultEvidence204.OutputWitness plan counter ⟨0,0⟩ :=
  ⟨committed,total_packet counter counter_inhabited,class_effects,no_default_output⟩

end Yulang.GeneralDictionaryDefaultGap206Counterexample
