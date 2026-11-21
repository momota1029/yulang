import Yulang.GeneralVersionedHistoryEvidence310
import Yulang.GeneralNominalVersionedMixedEvidenceReduction235
import Yulang.GeneralNominalVersionedMixedMaterialization237

set_option backward.isDefEq.respectTransparency false
/-! A history-covered node does not need prospective installation guards.
Only an uncovered selected node crosses the two residual source bridges. -/
namespace Yulang.GeneralVersionedRecursiveBridge310
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedTransport231 (extendedPlan)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂)

def ReplayFrame (registry : Registry) (state : State roles) (focus : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  ∃ old ∈ state.plans, ∃ reserved atoms allocated,
    Frame (Compiled registry) state.core focus key (extendedPlan reserved atoms allocated old) ∧
    children = GeneralNominalVersionedFrame231.children (extendedPlan reserved atoms allocated old).packet

def CurrentCandidate (registry : Registry) (state : State roles) (focus : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (effect : Effect roles) : Prop :=
  effect.registry = Compiled registry ∧ effect.snapshot = state.core ∧
  effect.plan.packet.site.occurrence = focus ∧ effect.plan.packet.declaration.id = key ∧
  GeneralNominalVersionedFrame231.children effect.plan.packet = children

def PendingCase (registry : Registry) (state : State roles) (root focus : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  (boundary roles).Checked registry ∧
  B4TargetV8.Reachable (boundary roles) registry root state ∧
  (focus = root ∨ Generated state.core.erased.current root focus) ∧
  (boundary roles).Stable registry state focus ∧
  Local registry state focus (.selected key children) ∧ (∃ m, Models state m) ∧
  ¬ ReplayFrame registry state focus key children

def ChoiceBridge (roles : Roles.RoleDecls) : Prop :=
  ∀ registry state (root focus : Occurrence roles) key children effect,
    PendingCase registry state root focus key children →
    CurrentCandidate registry state focus key children effect →
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet

def JointBridge (roles : Roles.RoleDecls) : Prop :=
  ∀ registry state (root focus : Occurrence roles) key children effect,
    PendingCase registry state root focus key children →
    CurrentCandidate registry state focus key children effect →
    GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current effect.plan.packet →
    ∃ m, GeneralNominalVersionedMixedMaterialization237.Residual state effect m

theorem enabled {registry : Registry} {state : State roles} {root focus : Occurrence roles}
    {effect : Effect roles} {key : Nat} {children : List (Occurrence roles)}
    (openCase : PendingCase registry state root focus key children)
    (candidate : CurrentCandidate registry state focus key children effect)
    (choose : ChoiceBridge roles) (joint : JointBridge roles) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) state effect := by
  obtain ⟨checked,path,reached,stable,selected,inhabited,missing⟩ := openCase
  have pick : Local registry state effect.plan.packet.site.occurrence (.selected key children) :=
    candidate.2.2.1.symm ▸ selected
  have choice := choose registry state root focus key children effect
    ⟨checked,path,reached,stable,selected,inhabited,missing⟩ candidate
  have common := joint registry state root focus key children effect
    ⟨checked,path,reached,stable,selected,inhabited,missing⟩ candidate choice
  exact (GeneralNominalVersionedMixedMaterialization237.source_installable_iff checked path pick
    candidate.1 candidate.2.1).mpr ⟨choice,common⟩

theorem node_and_edges {registry : Registry} {state : State roles} {root focus : Occurrence roles}
    {key : Nat} {children : List (Occurrence roles)} {m : Assignment}
    (choose : ChoiceBridge roles) (joint : JointBridge roles)
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (reached : focus = root ∨ Generated state.core.erased.current root focus)
    (stable : (boundary roles).Stable registry state focus)
    (selected : Local registry state focus (.selected key children))
    (valid : Models state m)
    (actual : All₂ (Evidence (Compiled registry) state.core m) children dictionaries) :
    Evidence (Compiled registry) state.core m focus (.node key dictionaries) ∧
      ∀ child ∈ children, Generated state.core.erased.current root child := by
  classical
  by_cases replay : ReplayFrame registry state focus key children
  · obtain ⟨old,member,rs,ats,allocated,frame,order⟩ := replay
    obtain ⟨tree,edges⟩ := GeneralVersionedHistoryEvidence310.from_recorded_extension checked path member
      rs ats allocated frame order valid actual
    exact ⟨tree,edges reached⟩
  · obtain ⟨effect,g,s,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect checked path selected
    have active := GeneralVersionedRecursiveBridge310.enabled
      (effect := effect) ⟨checked,path,reached,stable,selected,⟨m,valid⟩,replay⟩ ⟨g,s,o,k,c⟩ choose joint
    have localPick := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp selected
    exact ⟨GeneralNominalVersionedMixedStableEvidence235.selected_node stable active o localPick valid actual,
      fun _ member => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children
        stable active o localPick reached member⟩

theorem evidenceNode {roles : Roles.RoleDecls} (choose : ChoiceBridge roles) (joint : JointBridge roles) :
    B4SkeletonV8.EvidenceNode (boundary roles) := by
  intro registry checked state root path m valid focus key children dictionaries reached stable _ selected childProofs
  exact (node_and_edges choose joint checked path reached stable selected valid childProofs).1

end Yulang.GeneralVersionedRecursiveBridge310
