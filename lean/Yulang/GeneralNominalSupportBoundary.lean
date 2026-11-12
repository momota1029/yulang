import Yulang.GeneralNominalSupportSteps
import Yulang.GeneralNominalReobservationBoundary

/-! The provenance-aware boundary retains full-journal K2 and survivor facts.
Unsupported expansion is inspection pending, below K2 in V3 priority. No
progress or evidence-completeness theorem is included in this package. -/
namespace Yulang.GeneralNominalSupportBoundary

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open CommonRoleOutermostResolver (Frontier Child)
open B4TargetV5

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := Tracked roles
  Demand := Occurrence roles
  Model := GeneralNominalCommonBridge.Assignment

def SupportPending (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ¬ ∃ support, DecisionGuard state registry root support

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) where
  Checked := (GeneralNominalFeedbackK2.fields roles).Checked
  Models := fun state => Models state.current
  RootPending := fun registry state => (GeneralNominalFeedbackK2.fields roles).RootPending registry state.current
  RootK2 := fun registry state => (GeneralNominalFeedbackK2.fields roles).RootK2 registry state.current
  CandidateK2 := fun registry state => (GeneralNominalFeedbackK2.fields roles).CandidateK2 registry state.current
  InspectionPending := fun registry state root =>
    (GeneralNominalFeedbackK2.fields roles).InspectionPending registry state.current root ∨ SupportPending registry state root
  Survivor := fun registry state => (GeneralNominalFeedbackK2.fields roles).Survivor registry state.current
  Reorders := (GeneralNominalFeedbackK2.fields roles).Reorders
  DictionaryEquivalent := (GeneralNominalFeedbackK2.fields roles).DictionaryEquivalent

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := GeneralNominalSupportSteps.Step
  Stable := GeneralNominalSupportSteps.Stable
  Generated := fun _ state => Generated state.current
  Evidence := fun registry state => GeneralDictionaryFeedbackEvidence.evidence roles registry state.current

def boundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) where
  toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (remaining roles)
  Initial := fun registry root state => ∃ context,
    GeneralNominalSourceFormation.InitialSource registry context root ∧ state = GeneralNominalSupport.initial context root

abbrev Local (registry : Registry) (state : Tracked roles) :=
  GeneralNominalLocalBoundary.Local (fields roles) registry state

theorem local_correspondence (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔ Local registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (remaining roles) frontier).symm

theorem local_total (registry : Registry) (checked : Checked registry) (state : Tracked roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  GeneralNominalLocalBoundary.local_total (fun key first last one two =>
    GeneralNominalRecursiveCandidates.survivor_children_functional registry checked state.current.context root key first last one two)

noncomputable def frontiers (roles : Roles.RoleDecls) : B4SkeletonV3.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then
        Classical.choose (local_total registry checked state root) else .pending
      Local := B4TargetV3.Local (boundary roles).toSourceBoundary registry state }

variable {roles : Roles.RoleDecls}

theorem closure (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalSupportSteps.closure halted

theorem stepModels (registry : Registry) (_checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : Tracked roles)
    (_reachable : Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalSupportSteps.stepModels step

theorem localIdentity (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state := rfl

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (demand : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    (frontiers roles registry state).frontier demand = frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary registry state demand frontier := by
  classical
  have valid := Classical.choose_spec (local_total registry checked.2 state demand)
  change (if checked : Checked registry then Classical.choose (local_total registry checked state demand) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  constructor
  · intro same
    rw [same] at valid
    exact (local_correspondence registry state demand frontier).mpr valid
  · intro given
    exact GeneralNominalLocalBoundary.local_functional valid ((local_correspondence registry state demand frontier).mp given)

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary := GeneralDictionaryPayloadOrder.equivalent_refl dictionary

theorem initialReorders (registry other : Registry) (_checked : (boundary roles).Checked registry)
    (_checkedOther : (boundary roles).Checked other) (order : (boundary roles).Reorders registry other)
    (state : Tracked roles) (root : Occurrence roles) (given : (boundary roles).Initial registry root state) :
    (boundary roles).Initial other root state := by
  obtain ⟨context,formed,same⟩ := given
  exact ⟨context,GeneralDictionaryInitialSource.source_reorders registry other order context root formed,same⟩

theorem reachable_formed (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (boundary roles) registry root state) : GeneralNominalSupportSteps.SourceFormed registry root state := by
  obtain ⟨start,⟨context,source,rfl⟩,path⟩ := reachable
  induction path with
  | refl => exact .initial context source
  | tail _ update ih => exact .update ih update

theorem support_pending (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (ready : ¬ GeneralNominalState.RootPending state.current.context.state root.demand)
    (blocked : SupportPending registry state root)
    (noRoot : ¬ GeneralNominalFeedbackK2.RootK2 state.current root)
    (noCandidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry state.current root) :
    Local registry state root .pending := .inspectionPending ready (Or.inr blocked) noRoot noCandidate

theorem rootK2_priority (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (cycle : GeneralNominalFeedbackK2.RootK2 state.current root) : Local registry state root .rejected :=
  .rejected ⟨GeneralNominalFeedbackK2.root_ready cycle,Or.inl cycle⟩

theorem candidateK2_priority (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (cycle : GeneralNominalFeedbackK2.CandidateK2 registry state.current root) : Local registry state root .rejected :=
  .rejected ⟨GeneralNominalFeedbackK2.candidate_ready cycle,Or.inr (Or.inl cycle)⟩

theorem selected_old (selected : Local registry state root (.selected key children)) :
    GeneralNominalFeedbackK2.Local registry state.current root (.selected key children) := by
  cases selected with
  | selected safe unique =>
    exact .selected ⟨safe.1,safe.2.1,safe.2.2.1,fun pending => safe.2.2.2 (Or.inl pending)⟩ unique

theorem selected_supported (selected : GeneralNominalFeedbackK2.Local registry state.current root (.selected key children))
    (support : List (Occurrence roles)) (guard : DecisionGuard state registry root support) :
    Local registry state root (.selected key children) := by
  cases selected with
  | selected safe unique =>
    refine .selected ⟨safe.1,safe.2.1,safe.2.2.1,?_⟩ unique
    rintro (old | unsupported)
    · exact safe.2.2.2 old
    · exact unsupported ⟨support,guard⟩

theorem install_selected {state : Tracked roles} (packet : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet)
    (support : List (Occurrence roles)) (guard : GeneralNominalSupportSteps.PacketGuard state packet support) :
    Local registry state packet.site.occurrence (.selected packet.declaration.id packet.children) := by
  apply selected_supported enabled.2.1 support
  have contexts := enabled.1.2.1
  have registries := enabled.1.1
  simpa only [contexts,registries] using guard.2

theorem whereAccessible_of_readback (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (readback : GeneralNominalCycleReadback.Readback roles registry state.current.context) :
    Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root := by
  have accessible := GeneralNominalCycleReadback.whereAccessible checked.2 readback root
  induction accessible with
  | intro root below ih =>
    refine Acc.intro root ?_
    rintro child ⟨key,children,selected,member⟩
    exact ih child ⟨key,children,GeneralNominalFeedbackK2.selected_legacy
      (selected_old ((local_correspondence registry state root _).mp selected)),member⟩

end Yulang.GeneralNominalSupportBoundary
