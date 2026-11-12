import Yulang.GeneralNominalFeedbackK2
import Yulang.GeneralNominalSourceFormation

/-! Journal-aware transitions with provenance-preserving emission. Installation
is gated by the journal graph before any further candidate is expanded. The
legacy transitions remain unchanged; equality feedback and certified refresh
preserve the entire journal's model set. -/
namespace Yulang.GeneralNominalFeedbackSteps

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging (Site)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles} {root : Occurrence roles}

abbrev Committed := @GeneralNominalCycleSteps.Committed
abbrev Refresh := @GeneralNominalCycleSteps.Refresh

def MergesClosed (state : State roles) (site : Site roles) : Prop :=
  ∀ other ∈ state.sites, GeneralNominalFeedbackSites.SameInputs state site other →
    Alias state site.occurrence.identity other.occurrence.identity

def Installable (registry : Registry) (state : State roles) (packet : Packet roles) : Prop :=
  GeneralNominalCycleSteps.Installable registry state packet ∧
    GeneralNominalFeedbackK2.Local registry state packet.site.occurrence (.selected packet.declaration.id packet.children) ∧
    MergesClosed state packet.site

def equate (state : State roles) (first last : Nat) : State roles :=
  { state with context := ⟨GeneralNominalState.extend state.context.state []
      (GeneralNominalAllocation.equations first (.var last)),state.context.interpretation⟩ }

def RawEqual (state : State roles) (first last : Nat) : Prop :=
  ∀ model, GeneralNominalState.Models state.context.state model →
    CommonNominalFullCarrier.Equivalent (model first).1 (model last).1

theorem equate_models (state : State roles) (first last : Nat)
    (equal : GeneralNominalFeedbackK2.Equal state first last) (model : Assignment) :
    Models (equate state first last) model ↔ Models state model := by
  change (GeneralNominalState.Models (GeneralNominalState.extend state.context.state [] _) model ∧ _) ↔ _
  rw [GeneralNominalState.extend_models]
  constructor
  · exact fun valid => ⟨valid.1.1,valid.2⟩
  · intro valid
    exact ⟨⟨valid.1,(GeneralNominalCaptureMerges.equations_exact model first (.var last)).mpr (equal model valid)⟩,valid.2⟩

theorem equate_feedback (state : State roles) (first last : Nat) : RawEqual (equate state first last) first last := by
  intro model valid
  exact (GeneralNominalCaptureMerges.equations_exact model first (.var last)).mp
    ((GeneralNominalState.extend_models ..).mp valid).2

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop where
  | enqueue (focus : Occurrence roles) : GeneralNominalState.Linked before.context.state focus.demand →
      (∀ site ∈ before.sites, site.occurrence ≠ focus) → At registry before focus (enqueue before focus)
  | install (packet : Packet roles) : Installable registry before packet → ¬ Committed before packet →
      At registry before packet.site.occurrence
        (GeneralNominalFeedbackSites.install before packet (GeneralNominalFeedbackSites.emitted packet))
  | merge (first last : Site roles) : first ∈ before.sites → last ∈ before.sites →
      GeneralNominalFeedbackSites.SameInputs before first last →
      ¬ Alias before first.occurrence.identity last.occurrence.identity →
      At registry before first.occurrence (merge before first last)
  | refresh (focus : Occurrence roles) (after : GeneralNominalCandidates.Context) :
      Refresh before after → (source : Nat) → source ∈ GeneralNominalState.sources before.context.state →
      ¬ GeneralNominalState.Known before.context.state source → GeneralNominalState.Known after.state source →
      At registry before focus (regenerate before after)
  | equate (focus : Occurrence roles) (first last : Nat) :
      first ∈ GeneralNominalState.sources before.context.state → last ∈ GeneralNominalState.sources before.context.state →
      GeneralNominalFeedbackK2.Equal before first last → ¬ RawEqual before first last →
      At registry before focus (equate before first last)

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before root focus ∧ At registry before focus after

theorem at_models (update : At registry before focus after) (model : Assignment)
    (valid : Models after model) : Models before model := by
  cases update with
  | enqueue => exact (enqueue_models ..).mp valid
  | install packet enabled _ =>
      exact ((GeneralNominalFeedbackSites.install_models _ packet _ enabled.1.2.1 model).mp valid).1
  | merge => exact ((merge_models ..).mp valid).1
  | refresh _ _ certificate _ _ _ _ => exact (GeneralNominalCycleSteps.refresh_models certificate model).mp valid
  | equate _ _ _ _ _ equal _ => exact (equate_models _ _ _ equal model).mp valid

theorem step_models (update : Step registry root before after) (model : Assignment)
    (valid : Models after model) : Models before model := at_models update.choose_spec.2 model valid

theorem steps_models (path : B4Target.Steps (Step registry root) before after) (model : Assignment)
    (valid : Models after model) : Models before model := by
  induction path with
  | refl => exact valid
  | tail _ step ih => exact ih (step_models step model valid)

theorem installed_committed (state : State roles) (packet : Packet roles) :
    Committed (GeneralNominalFeedbackSites.install state packet (GeneralNominalFeedbackSites.emitted packet)) packet := by
  refine ⟨fun model valid => valid.2.1 packet (by simp [GeneralNominalFeedbackSites.install]),?_⟩
  intro child member
  exact List.mem_append_right _ (List.mem_map.mpr ⟨child,member,rfl⟩)

theorem installed_children (state : State roles) (packet : Packet roles) (child : Occurrence roles)
    (member : child ∈ packet.children) :
    Generated (GeneralNominalFeedbackSites.install state packet (GeneralNominalFeedbackSites.emitted packet))
      packet.site.occurrence child := .child .root ((installed_committed state packet).2 child member)

theorem rootK2_never_installed (cycle : GeneralNominalFeedbackK2.RootK2 state packet.site.occurrence) :
    ¬ Installable registry state packet := by
  intro enabled
  cases enabled.2.1 with | selected safe _ => exact safe.2.1 cycle

theorem candidateK2_never_installed (cycle : GeneralNominalFeedbackK2.CandidateK2 registry state packet.site.occurrence) :
    ¬ Installable registry state packet := by
  intro enabled
  cases enabled.2.1 with | selected safe _ => exact safe.2.2.1 cycle

theorem pending_never_installed (pending : GeneralNominalState.RootPending state.context.state packet.site.occurrence.demand) :
    ¬ Installable registry state packet := by
  intro enabled
  exact GeneralNominalCycleSteps.pending_never_installed registry state packet pending enabled.1

def Stable (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state root focus → ∀ after, ¬ At registry state focus after

theorem halted_stable (halted : ∀ after, ¬ Step registry root state after) : Stable registry state root :=
  fun focus generated after update => halted after ⟨focus,generated,update⟩

theorem stable_halted (stable : Stable registry state root) : ∀ after, ¬ Step registry root state after := by
  rintro after ⟨focus,generated,update⟩
  exact stable focus generated after update

theorem stable_generated (stable : Stable registry state root) (generated : Generated state root child) :
    Stable registry state child := fun focus path => stable focus (generated_trans generated path)

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state root child → Stable registry state child :=
  ⟨halted_stable halted,fun _ generated => stable_generated (halted_stable halted) generated⟩

theorem stable_committed (stable : Stable registry state root) (packet : Packet roles)
    (generated : Generated state root packet.site.occurrence) (enabled : Installable registry state packet) :
    Committed state packet := by
  classical
  exact Classical.byContradiction fun novel => stable packet.site.occurrence generated _ (.install packet enabled novel)

theorem stable_equality_feedback (stable : Stable registry state root)
    (first last : Nat) (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state first last) : RawEqual state first last := by
  classical
  exact Classical.byContradiction fun novel => stable root .root _ (.equate root first last one two equal novel)

theorem stable_merges (stable : Stable registry state root) (first last : Site roles)
    (one : first ∈ state.sites) (two : last ∈ state.sites) (generated : Generated state root first.occurrence)
    (same : GeneralNominalFeedbackSites.SameInputs state first last) :
    Alias state first.occurrence.identity last.occurrence.identity := by
  classical
  exact Classical.byContradiction fun novel => stable first.occurrence generated _ (.merge first last one two same novel)

inductive SourceFormed (registry : Registry) (root : Occurrence roles) : State roles → Prop
  | initial (context) : GeneralNominalSourceFormation.InitialSource registry context root →
      SourceFormed registry root (initial context root)
  | update : SourceFormed registry root before → Step registry root before after → SourceFormed registry root after

theorem step_preserves (formed : SourceFormed registry root before) (step : Step registry root before after) :
    SourceFormed registry root after := .update formed step

theorem self_argument_blocks_trace (source : Nat)
    (argument : GeneralNominalFeedbackK2.Argument before source source)
    (path : B4Target.Steps (Step registry root) before after)
    (packet : Packet roles) (index : Fin (roles packet.site.occurrence.demand.role).arity)
    (same : (packet.site.occurrence.demand.arguments index).1 = source) :
    ¬ Installable registry after packet := by
  intro enabled
  have context := enabled.1.2.1
  obtain ⟨_,_,_,_,_,_,prepared,_,_,_,⟨model,valid,_⟩,_⟩ := enabled.1
  have linked : GeneralNominalState.Linked after.context.state packet.site.occurrence.demand := by
    rw [← context]
    exact prepared.2.1
  have ready : ¬ GeneralNominalState.RootPending after.context.state packet.site.occurrence.demand := by
    cases enabled.2.1 with | selected safe _ => exact safe.1
  have retained := GeneralNominalFeedbackK2.argument_model_restriction (steps_models path) argument
  have cycle := GeneralNominalFeedbackK2.root_self_argument after packet.site.occurrence linked ready index
    (by simpa only [same] using retained) model valid
  exact rootK2_never_installed cycle enabled

end Yulang.GeneralNominalFeedbackSteps
