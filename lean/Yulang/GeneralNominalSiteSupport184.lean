import Yulang.GeneralNominalRawSupport183

/-! Structural origin support for point, recovered and shared-emission raw sites.
These bounds expose actual constructors; trace-wide endpoint support is separate. -/
namespace Yulang.GeneralNominalSiteSupport184
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalDemandMerging
open GeneralNominalCenteredModelExtension (originSource)
open GeneralNominalCenteredEmptyFrame179 (rawSiteSources)

def Endpoints (site : Site roles) (names : List Nat) : Prop :=
  ∀ index, (site.occurrence.demand.arguments index).1 ∈ names ∧
    (site.occurrence.demand.arguments index).2 ∈ names

def Origins (site : Site roles) (names : List Nat) : Prop :=
  ∀ origin, some origin ∈ site.inputs → originSource origin ∈ names

theorem sources_iff (site : Site roles) (names : List Nat) :
    rawSiteSources site ⊆ names ↔ Endpoints site names ∧ Origins site names := by
  constructor
  · intro support
    refine ⟨?_,?_⟩
    · intro index
      constructor <;> apply support <;> apply List.mem_append_left _ <;>
        apply List.mem_flatten.mpr <;> refine ⟨_,List.mem_ofFn.mpr ⟨index,rfl⟩,?_⟩ <;> simp
    · intro origin member
      apply support
      exact List.mem_append_right _ (List.mem_map.mpr ⟨origin,
        List.mem_filterMap.mpr ⟨some origin,member,rfl⟩,rfl⟩)
  · rintro ⟨endpoints,origins⟩ name member
    rcases List.mem_append.mp member with member | member
    · obtain ⟨pair,member,inside⟩ := List.mem_flatten.mp member
      obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl
      · exact (endpoints index).1
      · exact (endpoints index).2
    · obtain ⟨origin,present,equalRoot⟩ := List.mem_map.mp member
      obtain ⟨entry,present,equal⟩ := List.mem_filterMap.mp present
      subst name
      exact origins origin (equal ▸ present)

theorem point_origins (occurrence : Occurrence roles)
    (endpoints : ∀ index, (occurrence.demand.arguments index).1 ∈ names) :
    Origins (pointSite occurrence) names := by
  intro origin member
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp member
  dsimp only at equal
  split at equal
  · cases equal
    exact endpoints index
  · cases equal

theorem point_sources (occurrence : Occurrence roles)
    (endpoints : ∀ index, (occurrence.demand.arguments index).1 ∈ names ∧
      (occurrence.demand.arguments index).2 ∈ names) :
    rawSiteSources (pointSite occurrence) ⊆ names :=
  (sources_iff _ _).mpr ⟨endpoints,point_origins occurrence (fun i => (endpoints i).1)⟩

theorem recover_origins (state : GeneralNominalSaturationState.State roles) (site : Site roles)
    (old : Origins site names) (endpoints : ∀ index, (site.occurrence.demand.arguments index).1 ∈ names) :
    Origins (GeneralNominalFeedbackSites.recover state site) names := by
  intro origin member
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp member
  change GeneralNominalFeedbackSites.recoverOrigin state site index = some origin at equal
  unfold GeneralNominalFeedbackSites.recoverOrigin at equal
  split at equal
  · rename_i prior recorded
    cases equal
    exact old origin (List.mem_of_getElem recorded)
  · split at equal
    · cases equal
      exact endpoints index
    · cases equal

theorem recover_sources (state : GeneralNominalSaturationState.State roles) (site : Site roles)
    (support : rawSiteSources site ⊆ names) :
    rawSiteSources (GeneralNominalFeedbackSites.recover state site) ⊆ names := by
  obtain ⟨endpoints,origins⟩ := (sources_iff _ _).mp support
  exact (sources_iff _ _).mpr ⟨endpoints,recover_origins state site origins (fun i => (endpoints i).1)⟩


def inheritedSources (packet : GeneralNominalSaturationState.Packet roles) : List Nat :=
  GeneralNominalState.sources packet.context.state ++ rawSiteSources packet.site

theorem inherited_roots (packet : GeneralNominalSaturationState.Packet roles) :
    GeneralNominalRawOrigin182.ReportRoots
      (GeneralNominalSharedCaptures.inheritedReport packet) (inheritedSources packet) := by
  apply GeneralNominalRawOrigin182.many_roots
  · intro slot
    exact List.mem_append_left _ (GeneralNominalAllocationSupport.slot_source _ slot)
  · intro index origin recorded
    have member : some origin ∈ packet.site.inputs := by
      cases entry : packet.site.inputs[index]? with
      | none => simp [entry] at recorded
      | some value =>
        have same : value = some origin := by simpa [entry] using recorded
        exact same ▸ List.mem_of_getElem? entry
    exact List.mem_append_right _ (((sources_iff _ _).mp (fun _ h => h)).2 origin member)

theorem usable_root (packet : GeneralNominalSaturationState.Packet roles)
    (usable : GeneralNominalSharedCaptures.Usable packet name origin) :
    originSource origin ∈ inheritedSources packet := by
  obtain ⟨capture,member,_,recorded⟩ := usable.1.1
  exact (inherited_roots packet).2.2 capture member origin recorded

theorem feedback_root (packet : GeneralNominalSaturationState.Packet roles)
    (recorded : GeneralNominalFeedbackSites.OriginAt packet child position origin) :
    originSource origin ∈ GeneralNominalState.sources packet.context.state := by
  obtain ⟨_,_,_,_,_,_,capture,member,_,recorded,_⟩ := recorded
  exact (GeneralNominalRawOrigin182.report_roots packet.context packet.declaration packet.bounds).2.2
    capture member origin recorded

theorem child_origin_sources (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (index : Fin (roles child.demand.role).arity)
    (origin : Origin) (recorded : GeneralNominalSharedEmission.childOrigin packet child index = some origin) :
    originSource origin ∈ inheritedSources packet ∨
      originSource origin = (child.demand.arguments index).1 := by
  classical
  unfold GeneralNominalSharedEmission.childOrigin at recorded
  split at recorded
  · rename_i found
    cases recorded
    obtain ⟨_,_,_,_,_,_,name,usable,_⟩ := Classical.choose_spec found
    exact Or.inl (usable_root packet usable)
  · unfold GeneralNominalFeedbackSites.childOrigin at recorded
    split at recorded
    · rename_i found
      cases recorded
      exact Or.inl (List.mem_append_left _ (feedback_root packet (Classical.choose_spec found)))
    · simp only [pointSite,List.getElem_ofFn] at recorded
      split at recorded
      · cases recorded
        exact Or.inr rfl
      · cases recorded

theorem child_sources (packet : GeneralNominalSaturationState.Packet roles)
    (child : Occurrence roles) (old : inheritedSources packet ⊆ names)
    (endpoints : ∀ index, (child.demand.arguments index).1 ∈ names ∧
      (child.demand.arguments index).2 ∈ names) :
    rawSiteSources (GeneralNominalSharedEmission.childSite packet child) ⊆ names := by
  apply (sources_iff _ _).mpr
  refine ⟨endpoints,?_⟩
  intro origin member
  obtain ⟨index,recorded⟩ := List.mem_ofFn.mp member
  rcases child_origin_sources packet child index origin recorded with inherited | lower
  · exact old inherited
  · exact lower ▸ (endpoints index).1

end Yulang.GeneralNominalSiteSupport184
