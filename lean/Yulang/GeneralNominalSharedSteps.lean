import Yulang.GeneralNominalSharedSupport
import Yulang.GeneralNominalSettledBudget

/-! An additive lazy relation: certified inherited origins are forwarded,
while only coherently read-back settled outputs justify expansion. -/
namespace Yulang.GeneralNominalSharedSteps
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalDemandMerging
open GeneralNominalCommonBridge (Assignment)

def PacketGuard (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) : Prop :=
  GeneralNominalValueSupport.PacketGuard state packet support ∧
  GeneralNominalSharedSupport.DecisionGuard packet.registry
    {state with current := {state.current with context := packet.context}} packet.site.occurrence ∧
  GeneralNominalSharedCaptures.GenerationGuard state packet ∧ GeneralNominalSharedCaptures.InputCoherence packet

noncomputable def install (state : Tracked roles) (packet : Packet roles) (_support : List (Occurrence roles)) : Tracked roles :=
  {state with
    current := GeneralNominalFeedbackSites.install state.current packet (GeneralNominalSharedEmission.emitted packet)
    facts := GeneralNominalSupportChoices.installedFacts state packet ++ state.facts}

noncomputable abbrev merge := @GeneralNominalSettledSteps.merge
abbrev Administrative := @GeneralNominalSettledSteps.Administrative

inductive At (registry : Registry) (before : Tracked roles) : Occurrence roles → Tracked roles → Prop
  | administrative (focus : Occurrence roles) (after : State roles) : Administrative registry before.current focus after →
      At registry before focus {before with current := after}
  | install (packet : Packet roles) (support : List (Occurrence roles)) :
      GeneralNominalFeedbackSteps.Installable registry before.current packet →
      ¬ GeneralNominalFeedbackSteps.Committed before.current packet → PacketGuard before packet support →
      At registry before packet.site.occurrence (install before packet support)
  | merge (first last : Site roles) (support : List (Occurrence roles)) :
      first ∈ before.current.sites → last ∈ before.current.sites →
      GeneralNominalFeedbackSites.SameInputs before.current first last →
      ¬ Alias before.current first.occurrence.identity last.occurrence.identity →
      GeneralNominalSupportChoices.MergeGuard before first last support →
      At registry before first.occurrence (merge before first last support)

def Step (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  ∃ focus, Generated before.current root focus ∧ At registry before focus after

def Stable (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ after, ¬ At registry state focus after

inductive SourceFormed (registry : Registry) (root : Occurrence roles) : Tracked roles → Prop
  | initial (context : GeneralNominalCandidates.Context) :
      GeneralNominalSourceFormation.InitialSource registry context root → SourceFormed registry root (initial context root)
  | update : SourceFormed registry root before → Step registry root before after → SourceFormed registry root after

theorem install_models (same : packet.context = state.current.context) (model : Assignment) :
    Models (install state packet support).current model ↔ Models state.current model ∧ packet.Holds model :=
  GeneralNominalFeedbackSites.install_models _ _ _ same model

theorem step_models (step : Step registry root before after) (model : Assignment)
    (valid : Models after.current model) : Models before.current model := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative _ _ action => exact (GeneralNominalSupportSteps.administrative_models action model).mp valid
  | install packet support enabled novel guard => exact ((install_models enabled.1.2.1 model).mp valid).1
  | merge first last support one two same novel guard => exact ((merge_models ..).mp valid).1

theorem at_edges (step : At registry before focus after) : ∀ edge ∈ before.current.edges, edge ∈ after.current.edges := by
  cases step with
  | administrative _ _ action =>
      exact (GeneralNominalReobservationSteps.at_extends (GeneralNominalSupportSteps.administrative_old action)).journal.edges
  | install => intro edge member; exact List.mem_append_left _ member
  | merge => exact fun _ member => member

theorem installed_committed (state : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles)) :
    GeneralNominalFeedbackSteps.Committed (install state packet support).current packet := by
  refine ⟨fun model valid => valid.2.1 packet (by simp [install,GeneralNominalFeedbackSites.install]),?_⟩
  intro child member
  exact List.mem_append_right _ (List.mem_map.mpr ⟨child,member,rfl⟩)

theorem missing_generation_blocks (missing : ¬ GeneralNominalSharedCaptures.GenerationGuard state packet) :
    ¬ PacketGuard state packet support := fun guard => missing guard.2.2.1

theorem leaf_guard (empty : packet.declaration.requirements = [])
    (coherent : GeneralNominalSharedCaptures.InputCoherence packet)
    (old : GeneralNominalValueSupport.PacketGuard state packet support)
    (heads : GeneralNominalSharedSupport.DecisionGuard packet.registry
      {state with current := {state.current with context := packet.context}} packet.site.occurrence) :
    PacketGuard state packet support := ⟨old,heads,GeneralNominalSharedCaptures.no_children_guard empty,coherent⟩

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state.current root child → Stable registry state child := by
  have stable : Stable registry state root := fun focus reached after step => halted after ⟨focus,reached,step⟩
  exact ⟨stable,fun child reached focus path => stable focus (generated_trans reached path)⟩

def Passive (registry : Registry) (before after : Tracked roles) : Prop :=
  GeneralNominalReobservationOrder.Update registry before.current after.current

theorem passive_accessible (registry : Registry) (state : Tracked roles) :
    Acc (fun next current => Passive registry current next) state := by
  have lift : ∀ current, Acc (fun next current => GeneralNominalReobservationOrder.Update registry current next) current →
      ∀ state : Tracked roles, state.current = current → Acc (fun next current => Passive registry current next) state := by
    intro current accessible
    induction accessible with
    | intro current below ih =>
        intro state equal
        refine Acc.intro state ?_
        intro next update
        exact ih next.current (equal ▸ update) next rfl
  exact lift state.current (GeneralNominalReobservationOrder.accessible registry _) state rfl

private def Recorded (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ site ∈ state.sites, site.occurrence = root) ∧
    ∀ parent child, (parent,child) ∈ state.edges → ∃ site ∈ state.sites, site.occurrence = child

private theorem recorded_update (recorded : Recorded before.current root) (action : At registry before focus after) :
    Recorded after.current root := by
  cases action with
  | administrative focus after action =>
      have sites := (GeneralNominalReobservationSteps.at_extends
        (GeneralNominalSupportSteps.administrative_old action)).journal.sites
      have edges : after.edges = before.current.edges := by cases action <;> rfl
      obtain ⟨site,member,same⟩ := recorded.1
      refine ⟨⟨site,sites site member,same⟩,?_⟩
      intro parent child member
      rw [edges] at member
      obtain ⟨site,present,same⟩ := recorded.2 parent child member
      exact ⟨site,sites site present,same⟩
  | merge => exact recorded
  | install packet support enabled novel guard =>
      obtain ⟨site,member,same⟩ := recorded.1
      refine ⟨⟨site,List.mem_append_left _ member,same⟩,?_⟩
      intro parent child member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨site,present,same⟩ := recorded.2 parent child old
        exact ⟨site,List.mem_append_left _ present,same⟩
      · obtain ⟨actual,present,equal⟩ := List.mem_map.mp added
        cases equal
        exact ⟨GeneralNominalSharedEmission.childSite packet child,
          List.mem_append_right _ (List.mem_map.mpr ⟨child,present,rfl⟩),rfl⟩

theorem generated_registered (formed : SourceFormed registry root state)
    (generated : Generated state.current root child) : ∃ site ∈ state.current.sites, site.occurrence = child := by
  have recorded : Recorded state.current root := by
    clear generated
    induction formed with
    | initial context source =>
        exact ⟨⟨pointSite root,List.mem_singleton_self _,rfl⟩,by intro _ _ impossible; cases impossible⟩
    | update _ step ih => exact recorded_update ih step.choose_spec.2
  cases generated with
  | root => exact recorded.1
  | child _ member => exact recorded.2 _ _ member
  | alias _ _ member _ => exact ⟨_,member,rfl⟩

theorem formed_step_cases {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {before after : Tracked roles} (formed : SourceFormed registry root before) (step : Step registry root before after) :
    Passive registry before after ∨ ∃ packet : Packet roles, ∃ support,
      Generated before.current root packet.site.occurrence ∧
      GeneralNominalFeedbackSteps.Installable registry before.current packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed before.current packet ∧
      PacketGuard before packet support ∧ after = install before packet support := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | install packet support enabled novel guard => exact Or.inr ⟨packet,support,generated,enabled,novel,guard,rfl⟩
  | merge first last support one two same novel guard => exact Or.inl (.ordinary (.merge first last one two same novel))
  | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
          obtain ⟨site,member,same⟩ := generated_registered formed generated
          exact False.elim (absent site member same)
      | refresh context certificate source member unknown known =>
          exact Or.inl (.ordinary (.refresh focus context certificate source member unknown known))
      | equate first last one two equal novel => exact Or.inl (.ordinary (.equate focus first last one two equal novel))
      | reobserve revision certificate improved => exact Or.inl (.reobserve revision certificate improved)

end Yulang.GeneralNominalSharedSteps
