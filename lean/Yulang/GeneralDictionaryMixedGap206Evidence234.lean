import Yulang.GeneralDictionaryMixedGap206Frame234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedGap206Evidence234
open GeneralDictionaryDefaultGap206Source (roles registry root model)
open GeneralDictionaryMixedGap206Refresh234 (refreshed)
open GeneralDictionaryMixedGap206Frame234
open GeneralNominalVersionedJournal232
open CommonNominalFullCarrier

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests refreshed.core root) :
    output = ⟨0,0⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [raw_sites] at present
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready refreshed.core root plan :=
  GeneralNominalCenteredHeadMatEffects.ready_of_wf GeneralDictionaryDefaultGap206Source.coverage
    (List.mem_singleton_self _) rfl (by
      intro output member
      cases request_exact member
      exact ⟨some (.var 0),rfl⟩)

theorem class_effects (assignment) (valid : Models refreshed assignment) :
    GeneralNominalVersionedEffects231.ClassEffects refreshed.core root plan assignment := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases request_exact member
    have same : body = .default 0 0 (.var 0) := Option.some.inj found.symm
    subst body
    have zero := valid.1.1.1.2.1 (0 : Fin 3) (.base .int) rfl
    have one := valid.1.1.1.2.1 (1 : Fin 3) (.base .int) rfl
    exact (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1)).mpr
      ⟨subtype_trans zero.1 one.2,subtype_trans one.1 zero.2⟩
  · intro first one last two _
    cases request_exact one
    cases request_exact two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem certificate (assignment) (valid : Models refreshed assignment) :
    GeneralNominalVersionedEvidence231.Certificate registry refreshed.core assignment root 37 [] plan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics frame children_empty.symm
    (packet_holds assignment valid) ready (class_effects assignment valid)

theorem evidence (assignment) (valid : Models refreshed assignment) :
    GeneralNominalVersionedEvidence231.Evidence registry refreshed.core assignment root (.node 37 []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨plan,certificate assignment valid⟩

end Yulang.GeneralDictionaryMixedGap206Evidence234
