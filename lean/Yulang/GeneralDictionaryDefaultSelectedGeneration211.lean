import Yulang.GeneralDictionaryDefaultRegistered211
import Yulang.GeneralDictionaryDefaultAvailability208

namespace Yulang.GeneralDictionaryDefaultSelectedGeneration211
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary Local)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem selected_generated
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : Local value state focus (.selected key children)) :
    (boundary roles).Generated value state root focus := by
  obtain ⟨plan,frame,_⟩ := GeneralDictionaryDefaultAvailability208.selected_frame reachable selected
  exact (GeneralDictionaryDefaultRegistered211.registered_iff_generated reachable).mp
    ⟨plan.packet.site,frame.raw_recorded,frame.occurrence_eq⟩

theorem classified_generated
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (selected : B4TargetV7.Classify (boundary roles) value state focus (.selected dictionary)) :
    (boundary roles).Generated value state root focus := by
  cases selected with
  | selected localRule children => exact selected_generated reachable localRule

theorem evidence_registered
    (evidence : GeneralDictionaryTotalEvidence206.Evidence registry state.core model focus dictionary) :
    ∃ site ∈ state.core.erased.current.sites, site.occurrence = focus := by
  have payload := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
  cases payload with
  | node instanceRule children =>
      obtain ⟨plan,certificate⟩ := instanceRule
      exact ⟨plan.packet.site,certificate.frame.raw_recorded,certificate.frame.occurrence_eq⟩

theorem evidence_generated
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (evidence : (boundary roles).Evidence value state model focus dictionary) :
    (boundary roles).Generated value state root focus :=
  (GeneralDictionaryDefaultRegistered211.registered_iff_generated reachable).mp
    (evidence_registered evidence)

end Yulang.GeneralDictionaryDefaultSelectedGeneration211
