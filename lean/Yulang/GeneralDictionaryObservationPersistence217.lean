import Yulang.GeneralDictionaryTopLevelSharing217
import Yulang.GeneralNominalCenteredHeadMatStepRefresh

/-! Reobserving a nominal descriptor does not rewrite previously emitted
occurrences or their actual centers. This does not establish any raw Survivor. -/
namespace Yulang.GeneralDictionaryObservationPersistence217
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalOriginTerms GeneralDictionaryTopLevelSharing217
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatStepJournal
variable {roles : Roles.RoleDecls}

theorem repeated_impossible (registry : Registry) (state : State roles)
    (model : Assignment) (root : Occurrence roles) (key name : Nat)
    (heads : ∀ declaration ∈ registry.declarations, declaration.id = key →
      declaration.normalHead = [.var name,.var name])
    (different : ∀ site ∈ state.core.sites, site.occurrence = root →
      ¬ Same model (.source (firstCenter site)) (.source (secondCenter site))) :
    GeneralDictionarySharingObstruction217.Impossible registry state.core model root key := by
  apply impossible registry state model root key name _ different
  intro declaration member identity
  simp only [GeneralNominalInspection.queries,heads declaration member identity,List.map_cons,List.map_nil,
    GeneralNominalInspection.translate]

theorem refresh_recorded (state : State roles) (context : GeneralNominalCandidates.Context) :
    (refresh state context).core.sites = state.core.sites ∧
      (refresh state context).core.erased.current.sites = state.core.erased.current.sites ∧
      (refresh state context).core.erased.current.edges = state.core.erased.current.edges := ⟨rfl,rfl,rfl⟩

theorem reobserve_recorded (state : State roles)
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    (change state revision.result).core.sites = state.core.sites ∧
      (change state revision.result).core.erased.current.sites = state.core.erased.current.sites ∧
      (change state revision.result).core.erased.current.edges = state.core.erased.current.edges := ⟨rfl,rfl,rfl⟩

theorem reobserve_impossible (registry : Registry) (state : State roles)
    (model : Assignment) (root : Occurrence roles) (key name : Nat)
    (heads : ∀ declaration ∈ registry.declarations, declaration.id = key →
      declaration.normalHead = [.var name,.var name])
    (different : ∀ site ∈ state.core.sites, site.occurrence = root →
      ¬ Same model (.source (firstCenter site)) (.source (secondCenter site)))
    (revision : GeneralNominalReobservationSteps.Revision state.core.erased.current) :
    GeneralDictionarySharingObstruction217.Impossible registry (change state revision.result).core model root key :=
  repeated_impossible registry (change state revision.result) model root key name heads different

theorem refresh_impossible (registry : Registry) (state : State roles)
    (model : Assignment) (root : Occurrence roles) (key name : Nat)
    (heads : ∀ declaration ∈ registry.declarations, declaration.id = key →
      declaration.normalHead = [.var name,.var name])
    (different : ∀ site ∈ state.core.sites, site.occurrence = root →
      ¬ Same model (.source (firstCenter site)) (.source (secondCenter site)))
    (context : GeneralNominalCandidates.Context) :
    GeneralDictionarySharingObstruction217.Impossible registry (refresh state context).core model root key :=
  repeated_impossible registry (refresh state context) model root key name heads different
end Yulang.GeneralDictionaryObservationPersistence217
