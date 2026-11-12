import Yulang.GeneralDictionaryOrdinarySelectedReplay

/-! Operationally restricted support traces: enqueue, entailed equality,
guarded installation and guarded merge are actual original rules. No context
Extension premise is accepted on an edge; it is proved from each constructor.
Descriptor refresh/reobservation are deliberately excluded. -/
namespace Yulang.GeneralDictionarySupportOrdinaryExecution
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDictionaryOrdinaryTrace
variable {roles : Roles.RoleDecls}

inductive At (registry : Registry) (before : Tracked roles) :
    Occurrence roles → Tracked roles → Prop where
  | enqueue (focus : Occurrence roles)
      (linked : GeneralNominalState.Linked before.current.context.state focus.demand)
      (absent : ∀ site ∈ before.current.sites, site.occurrence ≠ focus) :
      At registry before focus {before with current := GeneralNominalSaturationState.enqueue before.current focus}
  | equate (focus : Occurrence roles) (first last : Nat)
      (one : first ∈ GeneralNominalState.sources before.current.context.state)
      (two : last ∈ GeneralNominalState.sources before.current.context.state)
      (equal : GeneralNominalFeedbackK2.Equal before.current first last)
      (novel : ¬ GeneralNominalFeedbackSteps.RawEqual before.current first last) :
      At registry before focus {before with current := GeneralNominalFeedbackSteps.equate before.current first last}
  | install (packet : Packet roles) (support : List (Occurrence roles))
      (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
      (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current packet)
      (guard : PacketGuard before packet support) :
      At registry before packet.site.occurrence (GeneralNominalSupportSteps.install before packet support)
  | merge (first last : GeneralNominalDemandMerging.Site roles) (support : List (Occurrence roles))
      (one : first ∈ before.current.sites) (two : last ∈ before.current.sites)
      (same : GeneralNominalFeedbackSites.SameInputs before.current first last)
      (novel : ¬ Alias before.current first.occurrence.identity last.occurrence.identity)
      (guard : GeneralNominalSupportChoices.MergeGuard before first last support) :
      At registry before first.occurrence (GeneralNominalSupportSteps.merge before first last support)

def Step (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  ∃ focus, Generated before.current root focus ∧ At registry before focus after

theorem at_actual {registry : Registry} {before after : Tracked roles} {focus : Occurrence roles}
    (action : At registry before focus after) : GeneralNominalSupportSteps.At registry before focus after := by
  cases action with
  | enqueue focus linked absent => exact .administrative _ _ (.enqueue _ linked absent)
  | equate focus first last one two equal novel => exact .administrative _ _ (.equate _ _ _ one two equal novel)
  | install packet support enabled novel guard => exact .install packet support enabled novel guard
  | merge first last support one two same novel guard => exact .merge first last support one two same novel guard

theorem step_actual {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (update : Step registry root before after) : GeneralNominalSupportSteps.Step registry root before after :=
  ⟨update.choose,update.choose_spec.1,at_actual update.choose_spec.2⟩

theorem at_extension {registry : Registry} {before after : Tracked roles} {focus : Occurrence roles}
    (action : At registry before focus after) : Extension before.current.context after.current.context := by
  cases action with
  | enqueue focus linked absent => exact enqueue_extension _ _
  | equate focus first last one two equal novel => exact equate_extension _ _ _
  | install packet support enabled novel guard => exact install_extension _ _ enabled.1.2.1
  | merge first last support one two same novel guard => exact merge_extension _ _ _

theorem steps_actual {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior update ih => exact .tail ih (step_actual update)

theorem steps_extension {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (path : B4Target.Steps (Step registry root) before after) :
    Extension before.current.context after.current.context := by
  induction path with
  | refl => exact extension_refl _
  | tail prior update ih => exact extension_trans ih (at_extension update.choose_spec.2)

theorem steps_formed {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (formed : SourceFormed registry root before)
    (path : B4Target.Steps (Step registry root) before after) : SourceFormed registry root after := by
  induction path with
  | refl => exact formed
  | tail prior update ih => exact .update ih (step_actual update)

/-- Every historical packet has ordinary context growth after a trace built
from these real rules, provided that was true of the initial journal. -/
theorem packets_extension {registry : Registry} {root : Occurrence roles} {before after : Tracked roles}
    (old : ∀ packet ∈ before.current.packets, Extension packet.context before.current.context)
    (path : B4Target.Steps (Step registry root) before after) :
    ∀ packet ∈ after.current.packets, Extension packet.context after.current.context := by
  induction path with
  | refl => exact old
  | @tail middle finish prior update ih =>
    have retained : ∀ packet ∈ middle.current.packets, Extension packet.context finish.current.context :=
      fun packet member => extension_trans (ih packet member) (at_extension update.choose_spec.2)
    obtain ⟨focus,generated,action⟩ := update
    intro packet member
    cases action with
    | enqueue => exact retained packet member
    | equate => exact retained packet member
    | merge => exact retained packet member
    | install installed support enabled novel guard =>
      rcases List.mem_cons.mp member with rfl | old
      · exact packet_extension packet
      · exact retained packet old

/-- The empty initial journal discharges all historical growth assumptions. -/
theorem initial_packets_extension (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : Tracked roles)
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) after) :
    ∀ packet ∈ after.current.packets, Extension packet.context after.current.context :=
  packets_extension (by intro packet member; cases member) path

/-- Operational coverage from InitialSource. The only historical selection
coverage premise is an actual packet at this occurrence; its key and context
growth are derived. Arbitrary later ordinary installs and merges are allowed. -/
theorem initial_selected_replay (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    packet.declaration.id = key ∧ packet.children = children ∧
      GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus key children :=
  GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state
    (steps_formed (.initial context source) path) packet member
    (initial_packets_extension registry root context state path packet member) same key children selected model valid

theorem initial_selected_generated (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Generated state.current root focus ∧ ∀ child ∈ children, Generated state.current root child :=
  GeneralDictionaryOrdinarySelectedReplay.selected_generated registry root focus state
    (steps_formed (.initial context source) path) packet member
    (initial_packets_extension registry root context state path packet member) same key children selected model valid

/-- A fresh actual guarded installation followed by an ordinary-only suffix
supplies the recorded packet, source formation and context extension itself. -/
theorem installed_suffix_replay (registry : Registry) (root : Occurrence roles)
    (before after : Tracked roles) (formed : SourceFormed registry root before)
    (packet : Packet roles) (support : List (Occurrence roles))
    (generated : Generated before.current root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current packet)
    (guard : PacketGuard before packet support)
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupportSteps.install before packet support) after)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry after packet.site.occurrence (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    packet.declaration.id = key ∧ packet.children = children ∧
      GeneralDictionaryRecursiveEvidence.Instance registry after.current.context model packet.site.occurrence key children := by
  have initialStep : GeneralNominalSupportSteps.Step registry root before
      (GeneralNominalSupportSteps.install before packet support) :=
    ⟨_,generated,.install packet support enabled novel guard⟩
  have formedAfter := steps_formed (.update formed initialStep) path
  have member := GeneralDictionaryInstallationOrigin.steps_packets (steps_actual path)
    (packet := packet) (List.mem_cons_self ..)
  have growth := extension_trans (packet_extension packet) (steps_extension path)
  exact GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root packet.site.occurrence after
    formedAfter packet member growth rfl key children selected model valid

end Yulang.GeneralDictionarySupportOrdinaryExecution
