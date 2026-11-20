import Yulang.GeneralObservedMetadataBook290

/-! Constructor reads are distinct from named/targeted requests. Record
requests even if their body is missing or uses no constructor keys. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedMetadataRequestBook290
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredSteps (State)
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Output)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralObservedMetadataLive290 (liveBodies)

abbrev RequestBook := List (Output × Option Body)

def requestBook (s : State roles) (up : Occurrence roles) (plan : Plan roles) : RequestBook :=
  (GeneralRebaseExecutableRequests262.requests s up).map fun out =>
    (out,lookup roles plan.packet.declaration out.name)

theorem outputs (s : State roles) (up : Occurrence roles) (plan : Plan roles) :
    (requestBook s up plan).map Prod.fst = requests s up := by
  unfold requestBook
  rw [List.map_map,GeneralRebaseExecutableRequests262.requests_eq]
  exact List.map_id _

theorem body_list (s : State roles) (up : Occurrence roles) (plan : Plan roles) :
    (requestBook s up plan).filterMap Prod.snd = liveBodies s up plan := by
  unfold requestBook liveBodies
  rw [List.filterMap_map]
  rfl

theorem matches_request {s : State roles} {up : Occurrence roles} {plan : Plan roles}
    {out : Output} {body : Option Body} :
    (out,body) ∈ requestBook s up plan ↔
      out ∈ requests s up ∧ lookup roles plan.packet.declaration out.name = body := by
  unfold requestBook
  rw [GeneralRebaseExecutableRequests262.requests_eq]
  constructor
  · intro existsEntry
    obtain ⟨picked,recorded,same⟩ := List.mem_map.mp existsEntry
    cases same
    exact ⟨recorded,rfl⟩
  · rintro ⟨recorded,same⟩
    exact List.mem_map.mpr ⟨out,recorded,by rw [same]⟩

theorem changed_at_new_request {s t : State roles} {up : Occurrence roles} {plan : Plan roles}
    {out : Output} (old : out ∉ requests s up) (new : out ∈ requests t up) :
    requestBook s up plan ≠ requestBook t up plan := by
  intro eq
  apply old
  rw [← outputs s up plan,eq,outputs]
  exact new

theorem actual_alias_gains_request_book :
    let root := GeneralNominalCenteredHeadAllocMergeInstall.aSite.occurrence
    requestBook GeneralRebaseMergeRegression264.sample.core root GeneralRebaseMergeRegression264.plan ≠
      requestBook GeneralRebaseMergeRegression264.merged.core root GeneralRebaseMergeRegression264.plan :=
  changed_at_new_request GeneralRebaseMergeRegression264.last_absent GeneralRebaseMergeRegression264.last_present

end Yulang.GeneralObservedMetadataRequestBook290
