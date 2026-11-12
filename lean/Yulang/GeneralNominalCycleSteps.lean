import Yulang.GeneralNominalJointCandidates
import Yulang.GeneralNominalSaturationSteps

/-! Additive transitions using cycle-based local selection. The stored state,
packet conditions, fresh allocation and generated demands are unchanged. Old
transition and local definitions remain available under their original names.
A joint alias condition guards installation. Complete joint local classification
and total normalization remain separate obligations. -/
namespace Yulang.GeneralNominalCycleSteps

open GeneralDeclarations
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalDemandMerging (Site SameInputs)
open GeneralNominalSaturationState

def MergesClosed (state : State roles) (site : Site roles) : Prop :=
  ∀ other ∈ state.sites, SameInputs (Models state) site other →
    Alias state site.occurrence.identity other.occurrence.identity

/-- Guard a new installation against choices already recorded in its current
alias class. This is not a consistency theorem for later class merges. -/
def ChoiceCompatible (state : State roles) (packet : Packet roles) : Prop :=
  ∀ prior ∈ state.packets, Alias state packet.site.occurrence.identity prior.site.occurrence.identity →
    packet.declaration.id = prior.declaration.id

def Installable (registry : Registry) (state : State roles) (packet : Packet roles) : Prop :=
  packet.registry = registry ∧ packet.context = state.context ∧ packet.site ∈ state.sites ∧
    packet.declaration ∈ registry.declarations ∧
    packet.declaration.role = packet.site.occurrence.demand.role ∧
    GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds ∧
    GeneralNominalRecursiveCandidates.Prepared packet.registry packet.context packet.site.occurrence packet.declaration packet.checked ∧
    GeneralNominalCycleK2.Local registry state.context
      packet.site.occurrence (.selected packet.declaration.id packet.children) ∧
    ChoiceCompatible state packet ∧ MergesClosed state packet.site ∧
    (∃ model, Models state model ∧ packet.Holds model) ∧
    GeneralNominalJointCandidates.Joint registry state packet.site.occurrence packet.declaration.id

theorem installable_joint {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
    {packet : Packet roles} (enabled : Installable registry state packet) :
    GeneralNominalJointCandidates.Joint registry state packet.site.occurrence packet.declaration.id := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,joint⟩ := enabled
  exact joint

def Committed (state : State roles) (packet : Packet roles) : Prop :=
  (∀ model, Models state model → packet.Holds model) ∧
    ∀ child ∈ packet.children, (packet.site.occurrence,child) ∈ state.edges

structure Refresh (before : State roles) (after : GeneralNominalCandidates.Context) where
  refines : GeneralNominalRefinements.Refines before.context.state after.state
  interpretation : after.interpretation = before.context.interpretation
  exact : ∀ model, Models before model → GeneralNominalState.Models after.state model
  support : ∀ source ∈ GeneralNominalState.sources after.state, source ∈ GeneralNominalState.sources before.context.state

theorem refresh_models (certificate : Refresh before context) (model : Assignment) :
    Models (regenerate before context) model ↔ Models before model := by
  constructor
  · intro valid
    exact ⟨GeneralNominalRefinements.models certificate.refines model valid.1,valid.2⟩
  · intro valid
    exact ⟨certificate.exact model valid,valid.2⟩

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop where
  | enqueue (focus : Occurrence roles) : GeneralNominalState.Linked before.context.state focus.demand →
      (∀ site ∈ before.sites, site.occurrence ≠ focus) → At registry before focus (enqueue before focus)
  | install (packet : Packet roles) (emitted : Emitted packet) :
      Installable registry before packet → ¬ Committed before packet →
      At registry before packet.site.occurrence (install before packet emitted)
  | merge (first last : Site roles) : first ∈ before.sites → last ∈ before.sites →
      SameInputs (Models before) first last → ¬ Alias before first.occurrence.identity last.occurrence.identity →
      At registry before first.occurrence (merge before first last)
  | refresh (focus : Occurrence roles) (after : GeneralNominalCandidates.Context) :
      Refresh before after → (source : Nat) → source ∈ GeneralNominalState.sources before.context.state →
      ¬ GeneralNominalState.Known before.context.state source → GeneralNominalState.Known after.state source →
      At registry before focus (regenerate before after)

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before root focus ∧ At registry before focus after

structure Extends (before after : State roles) : Prop where
  models : ∀ model, Models after model → Models before model
  sites : ∀ site ∈ before.sites, site ∈ after.sites
  edges : ∀ edge ∈ before.edges, edge ∈ after.edges
  aliases : ∀ pair ∈ before.aliases, pair ∈ after.aliases
  known : ∀ source, GeneralNominalState.Known before.context.state source → GeneralNominalState.Known after.context.state source

theorem at_extends (update : At registry before focus after) : Extends before after := by
  cases update with
  | enqueue focus _ _ =>
      exact ⟨fun model valid => (enqueue_models before focus model).mp valid,
        fun _ member => List.mem_append_left _ member,fun _ member => member,fun _ member => member,
        fun _ known => known⟩
  | install packet emitted enabled novel =>
      refine ⟨fun model valid => ((install_models before packet emitted enabled.2.1 model).mp valid).1,
        fun _ member => List.mem_append_left _ member,fun _ member => List.mem_append_left _ member,
        fun _ member => member,?_⟩
      intro source known
      have refinement := GeneralNominalRefinements.installed packet.registry packet.context packet.site.occurrence
        packet.declaration packet.bounds
      apply refinement.known source
      simpa only [enabled.2.1] using known
  | merge first last _ _ _ _ =>
      exact ⟨fun model valid => ((merge_models before first last model).mp valid).1,
        fun _ member => member,fun _ member => member,fun _ member => List.mem_cons_of_mem _ member,
        fun _ known => known⟩
  | refresh focus context certificate source member unknown known =>
      refine ⟨?_,fun _ member => member,fun _ member => member,fun _ member => member,certificate.refines.known⟩
      intro model valid
      exact ⟨GeneralNominalRefinements.models certificate.refines model valid.1,valid.2⟩

theorem step_extends (update : Step registry root before after) : Extends before after :=
  at_extends update.choose_spec.2

theorem step_models (update : Step registry root before after) (model : Assignment)
    (valid : Models after model) : Models before model := (step_extends update).models model valid

theorem alias_monotone (growth : Extends before after) (equal : Alias before first last) : Alias after first last := by
  induction equal with
  | refl => exact .refl _
  | edge member => exact .edge (growth.aliases _ member)
  | symm _ ih => exact .symm ih
  | trans _ _ left right => exact .trans left right

theorem generated_monotone (growth : Extends before after) (generated : Generated before root child) :
    Generated after root child := by
  induction generated with
  | root => exact .root
  | child _ member ih => exact .child ih (growth.edges _ member)
  | alias _ one two equal ih => exact .alias ih (growth.sites _ one) (growth.sites _ two) (alias_monotone growth equal)

theorem installed_committed (state : State roles) (packet : Packet roles) (emitted : Emitted packet) :
    Committed (install state packet emitted) packet := by
  refine ⟨fun model valid => valid.2.1 packet (by simp [install]),?_⟩
  intro child member
  exact List.mem_append_right _ (List.mem_map.mpr ⟨child,member,rfl⟩)

theorem installed_children (state : State roles) (packet : Packet roles) (emitted : Emitted packet)
    (child : Occurrence roles) (member : child ∈ packet.children) :
    Generated (install state packet emitted) packet.site.occurrence child :=
  .child .root ((installed_committed state packet emitted).2 child member)

theorem merged_inputs (state : State roles) (first last : Site roles) :
    Alias (merge state first last) first.occurrence.identity last.occurrence.identity := .edge (by simp [merge])

theorem replay_does_not_add_information (registry : Registry) (state : State roles) (packet : Packet roles)
    (committed : Committed state packet) : ¬ (Installable registry state packet ∧ ¬ Committed state packet) :=
  fun ready => ready.2 committed

theorem pending_never_installed (registry : Registry) (state : State roles) (packet : Packet roles)
    (pending : GeneralNominalState.RootPending state.context.state packet.site.occurrence.demand) :
    ¬ Installable registry state packet := by
  intro enabled
  have classification := enabled.2.2.2.2.2.2.2.1
  cases classification with
  | selected safe _ => exact safe.1 pending

theorem rootK2_never_installed (registry : Registry) (state : State roles) (packet : Packet roles)
    (cycle : GeneralNominalCycleK2.RootK2 state.context.state packet.site.occurrence.demand) :
    ¬ Installable registry state packet := by
  intro enabled
  have classification := enabled.2.2.2.2.2.2.2.1
  cases classification with
  | selected safe _ => exact safe.2.1 cycle

theorem candidateK2_never_installed (registry : Registry) (state : State roles) (packet : Packet roles)
    (cycle : GeneralNominalCycleK2.CandidateK2 registry state.context packet.site.occurrence) :
    ¬ Installable registry state packet := by
  intro enabled
  have classification := enabled.2.2.2.2.2.2.2.1
  cases classification with
  | selected safe _ => exact safe.2.2.1 cycle

def Closed (registry : Registry) (state : State roles) (focus : Occurrence roles) : Prop :=
  (∀ packet, packet.site.occurrence = focus → Installable registry state packet → Committed state packet) ∧
  (∀ first ∈ state.sites, first.occurrence = focus → ∀ last ∈ state.sites,
    SameInputs (Models state) first last → Alias state first.occurrence.identity last.occurrence.identity) ∧
  ∀ context, Refresh state context → ∀ source ∈ GeneralNominalState.sources state.context.state,
    GeneralNominalState.Known context.state source → GeneralNominalState.Known state.context.state source

/-- Initialization is part of closure, even for a root with no prior journal entry. -/
def Registered (state : State roles) (focus : Occurrence roles) : Prop :=
  GeneralNominalState.Linked state.context.state focus.demand → ∃ site ∈ state.sites, site.occurrence = focus

def Stable (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state root focus → Registered state focus ∧ Closed registry state focus

theorem closed_iff_no_update : Registered state focus ∧ Closed registry state focus ↔ ∀ after, ¬ At registry state focus after := by
  constructor
  · intro closed after update
    cases update with
    | enqueue focus linked absent =>
        obtain ⟨site,member,equal⟩ := closed.1 linked
        exact absent site member equal
    | install packet emitted ready novel => exact novel (closed.2.1 packet rfl ready)
    | merge first last one two same novel => exact novel (closed.2.2.1 first one rfl last two same)
    | refresh _ context checked source member unknown known => exact unknown (closed.2.2.2 context checked source member known)
  · intro halted
    classical
    refine ⟨?_,?_,?_,?_⟩
    · intro linked
      apply Classical.byContradiction
      intro absent
      apply halted _ (.enqueue focus linked ?_)
      intro site member equal
      exact absent ⟨site,member,equal⟩
    · intro packet same ready
      apply Classical.byContradiction
      intro novel
      have update := At.install packet (pointEmitted packet) ready novel
      rw [same] at update
      exact halted _ update
    · intro first one same last two inputs
      apply Classical.byContradiction
      intro novel
      have update := At.merge (registry := registry) first last one two inputs novel
      rw [same] at update
      exact halted _ update
    · intro context checked source member known
      apply Classical.byContradiction
      intro unknown
      exact halted _ (.refresh focus context checked source member unknown known)

theorem halted_stable (halted : ∀ after, ¬ Step registry root state after) : Stable registry state root := by
  intro focus generated
  apply closed_iff_no_update.mpr
  intro after update
  exact halted after ⟨focus,generated,update⟩

theorem stable_generated (stable : Stable registry state root) (generated : Generated state root child) :
    Stable registry state child := fun focus path => stable focus (generated_trans generated path)

theorem stable_halted (stable : Stable registry state root) : ∀ after, ¬ Step registry root state after := by
  rintro after ⟨focus,generated,update⟩
  exact (closed_iff_no_update.mp (stable focus generated)) after update

theorem halted_closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state root child → Stable registry state child :=
  ⟨halted_stable halted,fun _ generated => stable_generated (halted_stable halted) generated⟩

theorem steps_models (steps : B4Target.Steps (Step registry root) before after) (model : Assignment)
    (valid : Models after model) : Models before model := by
  induction steps with
  | refl => exact valid
  | tail path step ih => exact ih (step_models step model valid)

end Yulang.GeneralNominalCycleSteps
