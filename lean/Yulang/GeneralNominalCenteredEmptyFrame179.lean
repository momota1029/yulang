import Yulang.GeneralNominalCenteredFrame179

/-! Full centered-model finite frames when the raw packet journal is empty.
Raw observed sites and the centered ledger may still be present. The missing
raw-model premise is discharged, rather than renamed. -/
namespace Yulang.GeneralNominalCenteredEmptyFrame179
open GeneralNominalCenteredFrame179 GeneralNominalCenteredModelExtension
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
variable {first last : Assignment}

 def rawSiteSources (site : GeneralNominalDemandMerging.Site roles) : List Nat :=
  (List.ofFn fun index => [(site.occurrence.demand.arguments index).1,
    (site.occurrence.demand.arguments index).2]).flatten ++
    (site.inputs.filterMap id).map originSource

 theorem raw_site_iff (site : GeneralNominalDemandMerging.Site roles)
    (same : Agree (rawSiteSources site) first last) :
    GeneralNominalSaturationState.SiteHolds site first ↔ GeneralNominalSaturationState.SiteHolds site last := by
  unfold GeneralNominalSaturationState.SiteHolds
  apply forall_congr'; intro index
  apply forall_congr'; intro origin
  apply forall_congr'; intro recorded
  have lower := same (site.occurrence.demand.arguments index).1
    (List.mem_append_left _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩))
  have upper := same (site.occurrence.demand.arguments index).2
    (List.mem_append_left _ (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,by simp⟩))
  have member : some origin ∈ site.inputs := List.mem_of_getElem? recorded
  have observed : originSource origin ∈ (site.inputs.filterMap id).map originSource :=
    List.mem_map.mpr ⟨origin,List.mem_filterMap.mpr ⟨some origin,member,rfl⟩,rfl⟩
  have root := same (originSource origin) (List.mem_append_right _ observed)
  simp only [observes_iff origin root,GeneralNominalCaptureMerges.Fits,lower,upper]

 def rawSources (state : GeneralNominalSaturationState.State roles) : List Nat :=
  GeneralNominalState.sources state.context.state ++ state.sites.flatMap rawSiteSources

 theorem raw_models_frame (state : GeneralNominalSaturationState.State roles)
    (empty : state.packets = []) (same : Agree (rawSources state) first last)
    (valid : GeneralNominalSaturationState.Models state first) :
    GeneralNominalSaturationState.Models state last := by
  refine ⟨source_models_same state.context.state
    (fun name member => same name (List.mem_append_left _ member)) valid.1,?_,?_⟩
  · intro packet member
    rw [empty] at member
    cases member
  · intro site member
    apply (raw_site_iff site ?_).mp (valid.2.2 site member)
    intro name present
    exact same name (List.mem_append_right _ (List.mem_flatMap.mpr ⟨site,member,present⟩))

 def fullSources (state : GeneralNominalCenteredSteps.State roles) : List Nat :=
  rawSources state.erased.current ++ ledgerSources state

 theorem centered_models_frame (state : GeneralNominalCenteredSteps.State roles)
    (empty : state.erased.current.packets = [])
    (same : Agree (fullSources state) first last)
    (valid : GeneralNominalCenteredSteps.Models state first) :
    GeneralNominalCenteredSteps.Models state last :=
  ledger_frame state (fun name member => same name (List.mem_append_right _ member)) valid
    (raw_models_frame state.erased.current empty
      (fun name member => same name (List.mem_append_left _ member)) valid.1)

 theorem centered_models_iff (state : GeneralNominalCenteredSteps.State roles)
    (empty : state.erased.current.packets = [])
    (same : Agree (fullSources state) first last) :
    GeneralNominalCenteredSteps.Models state first ↔ GeneralNominalCenteredSteps.Models state last :=
  ⟨centered_models_frame state empty same,
    centered_models_frame state empty (fun name member => (same name member).symm)⟩

 theorem centered_assign (state : GeneralNominalCenteredSteps.State roles)
    (empty : state.erased.current.packets = [])
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ fullSources state)
    (valid : GeneralNominalCenteredSteps.Models state first) :
    GeneralNominalCenteredSteps.Models state (assign first names values) :=
  centered_models_frame state empty (assign_agree names values _ outside) valid
end Yulang.GeneralNominalCenteredEmptyFrame179
