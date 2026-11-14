import Yulang.GeneralNominalCenteredHeadMatStepCache
import Yulang.GeneralNominalCenteredAdministrativeWhere

namespace Yulang.GeneralNominalCenteredHeadMatStepBoundary
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State initial)
open GeneralNominalCenteredHeadMatStepLocal (vocabulary fields OutputConflict)
variable {roles : Roles.RoleDecls}

def Initial (registry : Registry) (root : Occurrence roles) (state : State roles) : Prop :=
  ∃ context labels, GeneralNominalSourceFormation.InitialSource registry context root ∧
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
    GeneralNominalGroundAccessibility.GroundRoots context root labels ∧
    GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation ∧ state = initial context root

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := GeneralNominalCenteredHeadMatStepKernel.Step
  Stable := GeneralNominalCenteredHeadMatStepKernel.Stable
  Generated := fun _ state => GeneralNominalSaturationState.Generated state.core.erased.current
  Evidence := fun registry state => GeneralDictionaryFeedbackEvidence.evidence roles registry state.core.erased.current

def boundary (roles : Roles.RoleDecls) : B4TargetV6.SourceBoundary (vocabulary roles) where
  toV5 := { toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (remaining roles)
            Initial := Initial }
  OutputConflict := OutputConflict

abbrev Local (registry : Registry) (state : State roles) := B4TargetV6.Local (boundary roles) registry state

theorem local_iff : Local registry state root frontier ↔
    GeneralNominalCenteredHeadMatStepLocal.Local registry state root frontier := by
  constructor <;> intro chosen <;> cases chosen with
  | pending h => exact .pending h
  | inspectionPending a b c d => exact .inspectionPending a b c d
  | rejected h => exact .rejected h
  | ambiguous a b c d => exact .ambiguous a b c d
  | selected a b c => exact .selected a b c

theorem local_total (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier := by
  obtain ⟨frontier,chosen⟩ := GeneralNominalCenteredHeadMatStepLocal.local_total checked state root
  exact ⟨frontier,local_iff.mpr chosen⟩

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  B4TargetV6.local_functional one two

theorem reachable_cache (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    GeneralNominalCenteredHeadMatStepCache.Valid state := by
  obtain ⟨first,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  exact GeneralNominalCenteredHeadMatStepCache.steps_cache path (GeneralNominalCenteredHeadMatStepCache.initial_valid context root)

theorem stepModels (registry : Registry) (_checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles)
    (_reachable : B4TargetV6.Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  fun _ valid => GeneralNominalCenteredHeadMatStepKernel.stepModels step valid

theorem closure (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalCenteredHeadMatStepKernel.closure halted

theorem initialReorders (order : (boundary roles).Reorders first last)
    (given : (boundary roles).Initial first root state) : (boundary roles).Initial last root state := by
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := given
  exact ⟨context,labels,GeneralDictionaryInitialSource.source_reorders first last order context root source,
    point,ground,GeneralNominalCenteredHeadWFSource.coverage_reorders order coverage,rfl⟩

theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary := rfl

theorem selected_ready (selected : Local registry state root (.selected key children)) :
    GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady state root :=
  GeneralNominalCenteredHeadMatStepLocal.selected_ready (local_iff.mp selected)

def rank (state : State roles) (root : Occurrence roles) : Nat :=
  GeneralNominalCenteredAdministrativeWhere.ceiling state.core + 1 - root.identity

theorem selected_bounded (selected : Local registry state root (.selected key children)) :
    root.identity ≤ GeneralNominalCenteredAdministrativeWhere.ceiling state.core := by
  obtain ⟨site,member,same⟩ := (selected_ready selected).1
  exact GeneralNominalCenteredWhere.member_max _ _
    (List.mem_map.mpr ⟨site,member,congrArg Occurrence.identity same⟩)

theorem selected_child_above (selected : Local registry state root (.selected key children))
    (child : Occurrence roles) (member : child ∈ children) : root.identity < child.identity := by
  cases selected with
  | selected safe unique clear =>
      obtain ⟨_,declaration,_,checked,_,_,bounds,_,_,childrenEq⟩ := unique.1
      let packet : GeneralNominalSaturationState.Packet roles :=
        ⟨registry,state.core.erased.current.context,
          GeneralNominalDemandMerging.pointSite (GeneralNominalCenteredHeadCandidates.inputs root),declaration,checked,bounds⟩
      have same : children = packet.children := childrenEq
      exact GeneralNominalCenteredWhere.packet_child_above packet child (same ▸ member)

theorem child_rank (edge : Child (Local registry state) child root) : rank state child < rank state root := by
  obtain ⟨key,children,selected,member⟩ := edge
  have bounded := selected_bounded selected
  have above := selected_child_above selected child member
  unfold rank
  omega

theorem whereAccessible (registry : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (Local registry state)) root := by
  have all : ∀ n, ∀ root, rank state root = n → Acc (Child (Local registry state)) root := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro root equal
        exact Acc.intro root (fun child edge => ih _ (equal ▸ child_rank edge) child rfl)
  exact all _ root rfl

end Yulang.GeneralNominalCenteredHeadMatStepBoundary
