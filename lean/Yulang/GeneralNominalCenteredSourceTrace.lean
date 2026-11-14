import Yulang.GeneralNominalCenteredSteps
import Yulang.GeneralNominalIdentityJournal

/-! Structural and semantic invariants for the full centered relation.
These proofs do not require erasure into the older guarded relation. -/
namespace Yulang.GeneralNominalCenteredSourceTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalPatersonLineage

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

theorem configuration_step (step : Step registry root before after) :
    after.erased.current.context.state.seed = before.erased.current.context.state.seed ∧
    after.erased.current.context.state.constructors = before.erased.current.context.state.constructors ∧
    after.erased.current.context.interpretation = before.erased.current.context.interpretation := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action =>
    cases action with
    | refresh _ certificate _ _ _ _ => exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
    | enqueue | equate | reobserve => exact ⟨rfl,rfl,rfl⟩
  | refresh focus context certificate source member unknown known =>
    exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
  | merge => exact ⟨rfl,rfl,rfl⟩
  | install plan support enabled novel guard =>
    change plan.packet.context.state.seed = before.erased.current.context.state.seed ∧
      plan.packet.context.state.constructors = before.erased.current.context.state.constructors ∧
      plan.packet.context.interpretation = before.erased.current.context.interpretation
    rw [enabled.1.2.1]
    exact ⟨rfl,rfl,rfl⟩

theorem configuration_trace (path : B4Target.Steps (Step registry root) before after) :
    after.erased.current.context.state.seed = before.erased.current.context.state.seed ∧
    after.erased.current.context.state.constructors = before.erased.current.context.state.constructors ∧
    after.erased.current.context.interpretation = before.erased.current.context.interpretation := by
  induction path with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | tail path step ih =>
    have next := configuration_step step
    exact ⟨next.1.trans ih.1,next.2.1.trans ih.2.1,next.2.2.trans ih.2.2⟩

theorem source_step (step : Step registry root before after) :
    after.erased.source = before.erased.source ∧ after.sourceSites = before.sourceSites := by
  obtain ⟨focus,generated,action⟩ := step
  cases action <;> exact ⟨rfl,rfl⟩

theorem source_trace (path : B4Target.Steps (Step registry root) before after) :
    after.erased.source = before.erased.source ∧ after.sourceSites = before.sourceSites := by
  induction path with
  | refl => exact ⟨rfl,rfl⟩
  | tail path step ih =>
    have next := source_step step
    exact ⟨next.1.trans ih.1,next.2.trans ih.2⟩

def Recorded (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ site ∈ state.erased.current.sites, site.occurrence = root) ∧
    ∀ parent child, (parent,child) ∈ state.erased.current.edges →
      ∃ site ∈ state.erased.current.sites, site.occurrence = child

theorem recorded_step (known : Recorded before root) (step : Step registry root before after) : Recorded after root := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action =>
    have sites := (GeneralNominalReobservationSteps.at_extends
      (GeneralNominalSupportSteps.administrative_old action)).journal.sites
    have edges : after.edges = before.erased.current.edges := by cases action <;> rfl
    obtain ⟨site,member,same⟩ := known.1
    refine ⟨⟨site,sites site member,same⟩,?_⟩
    intro parent child member
    change (parent,child) ∈ after.edges at member
    rw [edges] at member
    obtain ⟨site,present,same⟩ := known.2 parent child member
    exact ⟨site,sites site present,same⟩
  | refresh | merge => exact known
  | install plan support enabled novel guard =>
    obtain ⟨site,member,same⟩ := known.1
    refine ⟨⟨site,List.mem_append_left _ member,same⟩,?_⟩
    intro parent child member
    rcases List.mem_append.mp member with old | added
    · obtain ⟨site,present,same⟩ := known.2 parent child old
      exact ⟨site,List.mem_append_left _ present,same⟩
    · obtain ⟨actual,present,equal⟩ := List.mem_map.mp added
      cases equal
      exact ⟨GeneralNominalSharedEmission.childSite plan.packet child,
        List.mem_append_right _ (List.mem_map.mpr ⟨child,present,rfl⟩),rfl⟩

theorem recorded_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : Recorded state root := by
  induction path with
  | refl => exact ⟨⟨GeneralNominalDemandMerging.pointSite root,List.mem_singleton_self _,rfl⟩,
      by intro _ _ member; cases member⟩
  | tail path step ih => exact recorded_step ih step

theorem generated_registered
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : GeneralNominalSaturationState.Generated state.erased.current root child) :
    ∃ site ∈ state.erased.current.sites, site.occurrence = child := by
  have known := recorded_trace path
  cases generated with
  | root => exact known.1
  | child _ member => exact known.2 _ _ member
  | alias _ _ member _ => exact ⟨_,member,rfl⟩

theorem sites_lineage (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.erased.current.sites,
      ∃ depth, Lineage registry context.state.seed root state.erased.current.packets depth site.occurrence := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨0,.root⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := generated_registered path generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      obtain ⟨depth,parent⟩ := ih plan.packet.site enabled.1.2.2.1
      have seed : plan.packet.context.state.seed = context.state.seed := by
        rw [enabled.1.2.1]
        exact (configuration_trace path).1
      have included : before.erased.current.packets ⊆ plan.packet :: before.erased.current.packets :=
        fun _ member => List.mem_cons_of_mem _ member
      intro site member
      change site ∈ before.erased.current.sites ++ plan.packet.children.map (GeneralNominalSharedEmission.childSite plan.packet) at member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨depth,lineage⟩ := ih site old
        exact ⟨depth,lineage_mono lineage included⟩
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        exact ⟨depth+1,.child plan.packet (List.mem_cons_self ..) enabled.1.1 seed enabled.1.2.2.2.1
          (lineage_mono parent included) present⟩

theorem packets_lineage (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets,
      ∃ depth, Lineage registry context.state.seed root state.erased.current.packets depth packet.site.occurrence := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro prior member
      have included : before.erased.current.packets ⊆ plan.packet :: before.erased.current.packets :=
        fun _ member => List.mem_cons_of_mem _ member
      rcases List.mem_cons.mp member with rfl | member
      · obtain ⟨depth,lineage⟩ := sites_lineage path plan.packet.site enabled.1.2.2.1
        exact ⟨depth,lineage_mono lineage included⟩
      · obtain ⟨depth,lineage⟩ := ih prior member
        exact ⟨depth,lineage_mono lineage included⟩

theorem packet_configuration (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ packet ∈ state.erased.current.packets,
      packet.context.state.seed = context.state.seed ∧ packet.declaration ∈ registry.declarations := by
  induction path with
  | refl => intro packet member; cases member
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro prior member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨(congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.seed) enabled.1.2.1).trans
          (configuration_trace path).1,enabled.1.2.2.2.1⟩
      · exact ih prior member

theorem plan_packets (path : B4Target.Steps (Step registry root) (initial context root) state) :
    state.plans.map Plan.packet = state.erased.current.packets := by
  induction path with
  | refl => rfl
  | tail path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action => cases action <;> exact ih
    | refresh | merge => exact ih
    | install => exact congrArg (List.cons _) ih

theorem all_models (path : B4Target.Steps (Step registry root) (initial context root) state)
    (valid : Models state model) : GeneralNominalSupport.AllModels state.erased model := by
  induction path with
  | refl => exact ⟨valid.1.1,by intro fact member; cases member⟩
  | @tail before after path step ih =>
    have prior := ih (step_models step model valid)
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative | refresh => exact prior
    | install plan support enabled novel guard =>
      have branch := (install_models enabled.1.2.1 model).mp valid |>.2
      obtain ⟨inputs,outputs⟩ := GeneralNominalCenteredSupport.split_packet branch
      refine ⟨prior.1,?_⟩
      intro fact member
      rcases List.mem_append.mp member with added | old
      · obtain ⟨dependencies,present,member⟩ := List.mem_flatMap.mp added
        rcases List.mem_cons.mp member with rfl | member
        · exact inputs.1
        · cases List.mem_singleton.mp member; exact outputs.1
      · exact prior.2 fact old
    | merge first last support one two same novel guard =>
      have atoms := (GeneralNominalSaturationState.merge_models before.erased.current first.observed last.observed model).mp valid.1 |>.2
      refine ⟨prior.1,?_⟩
      intro fact member
      rcases List.mem_append.mp member with added | old
      · obtain ⟨dependencies,present,rfl⟩ := List.mem_map.mp added
        exact atoms
      · exact prior.2 fact old

theorem plan_models (path : B4Target.Steps (Step registry root) (initial context root) state)
    (member : plan ∈ state.plans) (valid : Models state model) : plan.Holds model :=
  ⟨valid.1.2.1 plan.packet ((plan_packets path) ▸ List.mem_map.mpr ⟨plan,member,rfl⟩),valid.2.2 plan member⟩

theorem trusted_models (path : B4Target.Steps (Step registry root) (initial context root) state)
    (trusted : GeneralNominalCenteredSupport.Trusted state.erased state.sourceSites state.plans facts)
    (valid : Models state model) : GeneralNominalCenteredSupport.Models state.erased state.sourceSites facts model := by
  have all := all_models path valid
  refine ⟨all.1,fun site member => valid.2.1 site (state.sourceRecorded site member),?_⟩
  induction trusted with
  | source => intro fact member; cases member
  | legacy facts readbacks trusted =>
    intro fact member
    obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
    exact all.2 old (GeneralNominalSettledSupport.trusted_members (GeneralNominalSharedSupport.trusted_old trusted) old present)
  | input plan support previous recorded member readback ih =>
    intro fact present
    rcases List.mem_cons.mp present with rfl | present
    · exact (GeneralNominalCenteredSupport.split_packet (plan_models path recorded valid)).1
    · exact ih fact present
  | output plan support previous recorded member included settled ih =>
    intro fact present
    rcases List.mem_cons.mp present with rfl | present
    · exact (GeneralNominalCenteredSupport.split_packet (plan_models path recorded valid)).2
    · exact ih fact present
  | merge first last support previous member holds same ih =>
    intro fact present
    rcases List.mem_cons.mp present with rfl | present
    · exact all.2 _ member
    · exact ih fact present

theorem trusted_inhabited (path : B4Target.Steps (Step registry root) (initial context root) state)
    (trusted : GeneralNominalCenteredSupport.Trusted state.erased state.sourceSites state.plans facts)
    (inhabited : ∃ model, Models state model) :
    ∃ model, GeneralNominalCenteredSupport.Models state.erased state.sourceSites facts model := by
  obtain ⟨model,valid⟩ := inhabited
  exact ⟨model,trusted_models path trusted valid⟩

end Yulang.GeneralNominalCenteredSourceTrace
