import Yulang.GeneralNominalCompoundEmission

/-! Additive recovery registration and journal-relative sharing interfaces.
These operations are not asserted to be steps of the frozen relation. -/
namespace Yulang.GeneralNominalRecoveredProvenance
open GeneralNominalSaturationState GeneralNominalDemandMerging
open GeneralNominalRecursiveInspection GeneralNominalFeedbackSites
open GeneralNominalSharedCaptures
open GeneralNominalCommonBridge (Assignment)

noncomputable def packet (state : State roles) (original : Packet roles) : Packet roles :=
  {original with site := recover state original.site}

theorem packet_holds (state : State roles) (original : Packet roles) (model : Assignment) :
    (packet state original).Holds model ↔ original.Holds model := Iff.rfl

theorem packet_children (state : State roles) (original : Packet roles) :
    (packet state original).children = original.children := rfl

theorem report_agrees (state : State roles) (original : Packet roles) :
    inheritedReport (packet state original) =
      GeneralNominalActualInspectionSteps.inspection state original := rfl

noncomputable def register (state : State roles) (site : Site roles) : State roles :=
  {state with sites := state.sites ++ [recover state site]}

theorem register_models (state : State roles) (site : Site roles) (present : site ∈ state.sites)
    (model : Assignment) : Models (register state site) model ↔ Models state model := by
  constructor
  · intro valid
    exact ⟨valid.1,valid.2.1,fun current member => valid.2.2 current (List.mem_append_left _ member)⟩
  · intro valid
    refine ⟨valid.1,valid.2.1,?_⟩
    intro current member
    rcases List.mem_append.mp member with old | added
    · exact valid.2.2 current old
    · obtain rfl := List.mem_singleton.mp added
      exact recover_sound state site model valid (valid.2.2 site present)

theorem recovered_registered (state : State roles) (site : Site roles) :
    recover state site ∈ (register state site).sites :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem recovery_fills (state : State roles) (site : Site roles)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (missing : site.inputs[index.val]? = some none)
    (equal : EndpointEqual state (site.occurrence.demand.arguments index)) :
    (recover state site).inputs[index.val]? =
      some (some (.source (site.occurrence.demand.arguments index).1)) :=
  GeneralNominalCompoundRecovery.root_recovered state site index missing equal

/-- The old ledger is needed here: recovery is not justified by a packet's
private models alone. Promotion into head evidence still uses Trusted. -/
def Usable (state : State roles) (original : Packet roles) (name : Nat) (origin : Origin) : Prop :=
  Captured (packet state original) (fun model => Models state model ∧ original.Holds model) name origin ∧
    ∀ model, Models state model → original.Holds model →
      (∃ actual, Observes model origin actual) ∧
      ∀ actual, Observes model origin actual → GeneralNominalCaptureMerges.Fits model
        ((GeneralNominalPacketSupport.capture original).inputs name) actual

def Generation (state : State roles) (original : Packet roles) : Prop :=
  ∀ name, Needed original name → ∃ origin, Usable state original name origin

theorem usable_of_private (state : State roles) (original : Packet roles)
    (given : GeneralNominalSharedCaptures.Usable (packet state original) name origin) :
    Usable state original name origin := by
  refine ⟨⟨given.1.1,?_⟩,?_⟩
  · intro captured member same
    obtain ⟨other,recorded,all⟩ := given.1.2 captured member same
    exact ⟨other,recorded,fun model valid => all model valid.2⟩
  · intro model _ valid
    exact given.2 model valid

theorem generation_of_private (state : State roles) (original : Packet roles)
    (given : GenerationGuard tracked (packet state original)) : Generation state original := by
  intro name needed
  obtain ⟨origin,usable⟩ := given name needed
  exact ⟨origin,usable_of_private state original usable⟩

/-- A replacement emitter may use the current journal, without strengthening
the ordinary model set. Exact child occurrences are still mandatory. -/
structure Emission (state : State roles) (original : Packet roles) where
  sites : List (Site roles)
  exact : sites.map Site.occurrence = original.children
  sound : ∀ model, Models state model → original.Holds model →
    ∀ site ∈ sites, SiteHolds site model

noncomputable def preexistingEmission (state : State roles) (original : Packet roles) : Emission state original where
  sites := (GeneralNominalSharedEmission.emitted original).sites.map (recover state)
  exact := by
    simpa only [List.map_map,Function.comp_def,recover] using
      (GeneralNominalSharedEmission.emitted original).exact
  sound := by
    intro model old valid site member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    exact recover_sound state prior model old ((GeneralNominalSharedEmission.emitted original).sound model valid prior present)

/-- New packet equations can establish fresh compound endpoint equality.
The temporary journal is used for recovery, not for trusted head promotion. -/
noncomputable def recoveredEmission (state : State roles) (original : Packet roles)
    (same : original.context = state.context) : Emission state original where
  sites := (GeneralNominalSharedEmission.emitted original).sites.map
    (recover (GeneralNominalFeedbackSites.install state original (GeneralNominalSharedEmission.emitted original)))
  exact := by
    simpa only [List.map_map,Function.comp_def,recover] using
      (GeneralNominalSharedEmission.emitted original).exact
  sound := by
    intro model old valid site member
    obtain ⟨prior,present,rfl⟩ := List.mem_map.mp member
    have provisional := (GeneralNominalFeedbackSites.install_models state original
      (GeneralNominalSharedEmission.emitted original) same model).mpr ⟨old,valid⟩
    exact recover_sound _ prior model provisional
      ((GeneralNominalSharedEmission.emitted original).sound model valid prior present)

def install (state : State roles) (original : Packet roles) (emission : Emission state original) : State roles :=
  {state with
    context := original.privateContext
    packets := original :: state.packets
    sites := state.sites ++ emission.sites
    edges := state.edges ++ original.children.map (fun child => (original.site.occurrence,child))}

theorem recovered_emission_fills (state : State roles) (original : Packet roles)
    (same : original.context = state.context) (site : Site roles)
    (present : site ∈ (GeneralNominalSharedEmission.emitted original).sites)
    (index : Fin (roles site.occurrence.demand.role).arity)
    (missing : site.inputs[index.val]? = some none)
    (equal : EndpointEqual
      (GeneralNominalFeedbackSites.install state original (GeneralNominalSharedEmission.emitted original))
      (site.occurrence.demand.arguments index)) :
    ∃ recovered ∈ (recoveredEmission state original same).sites,
      recovered.occurrence = site.occurrence ∧
      recovered.inputs[index.val]? = some (some (.source (site.occurrence.demand.arguments index).1)) :=
  ⟨recover _ site,List.mem_map.mpr ⟨site,present,rfl⟩,rfl,recovery_fills _ site index missing equal⟩

theorem install_models (state : State roles) (original : Packet roles) (emission : Emission state original)
    (same : original.context = state.context) (model : Assignment) :
    Models (install state original emission) model ↔ Models state model ∧ original.Holds model := by
  constructor
  · rintro ⟨_,packets,sites⟩
    have current := packets original (List.mem_cons_self ..)
    have old := (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ current).1
    rw [same] at old
    exact ⟨⟨old,fun p hp => packets p (List.mem_cons_of_mem _ hp),
      fun site hs => sites site (List.mem_append_left _ hs)⟩,current⟩
  · rintro ⟨old,current⟩
    refine ⟨current.1,?_,?_⟩
    · intro p member
      rcases List.mem_cons.mp member with rfl | member
      · exact current
      · exact old.2.1 p member
    · intro site member
      rcases List.mem_append.mp member with prior | generated
      · exact old.2.2 site prior
      · exact emission.sound model old current site generated

end Yulang.GeneralNominalRecoveredProvenance
