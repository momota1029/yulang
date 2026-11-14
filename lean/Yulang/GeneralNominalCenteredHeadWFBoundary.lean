import Yulang.GeneralNominalCenteredHeadWFSource

set_option backward.isDefEq.respectTransparency false

/-! The head-step boundary restricted to sources with constructor coverage.
Steps, models, diagnostics, refresh and the canonical executor are unchanged. -/
namespace Yulang.GeneralNominalCenteredHeadWFBoundary
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadStepEffects (State)
open GeneralNominalCenteredHeadStepBoundary (vocabulary)
open GeneralNominalCenteredHeadWFSource
variable {roles : Roles.RoleDecls}

def Initial (registry : Registry) (root : Occurrence roles) (state : State roles) : Prop :=
  GeneralNominalCenteredHeadStepBoundary.Initial registry root state ∧
    Coverage registry state.core.erased.current.context.interpretation

def boundary (roles : Roles.RoleDecls) : B4TargetV6.SourceBoundary (vocabulary roles) :=
  { GeneralNominalCenteredHeadStepBoundary.boundary roles with
    toV5 := { (GeneralNominalCenteredHeadStepBoundary.boundary roles).toV5 with Initial := Initial } }

abbrev Local (registry : Registry) (state : State roles) := B4TargetV6.Local (boundary roles) registry state

theorem initial_old (initial : (boundary roles).Initial registry root state) :
    (GeneralNominalCenteredHeadStepBoundary.boundary roles).Initial registry root state := initial.1

theorem reachable_old (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    B4TargetV6.Reachable (GeneralNominalCenteredHeadStepBoundary.boundary roles) registry root state := by
  obtain ⟨first,initial,path⟩ := reachable
  exact ⟨first,initial.1,path⟩

theorem reachable_coverage (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    Coverage registry state.core.erased.current.context.interpretation := by
  obtain ⟨first,initial,path⟩ := reachable
  rw [(GeneralNominalCenteredHeadStepTrace.configuration_trace path).2.2]
  exact initial.2

theorem initial_reorders (order : GeneralRegistryReordering.Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state :=
  ⟨GeneralNominalCenteredHeadStepRegistry.initial_reorders order initial.1,coverage_reorders order initial.2⟩

theorem local_iff : Local registry state demand frontier ↔
    GeneralNominalCenteredHeadStepBoundary.Local registry state demand frontier := by
  constructor <;> intro localRule <;> cases localRule with
  | pending h => exact .pending h
  | inspectionPending a b c d => exact .inspectionPending a b c d
  | rejected h => exact .rejected h
  | ambiguous a b c d => exact .ambiguous a b c d
  | selected a b c => exact .selected a b c

theorem local_eq (registry : Registry) (state : State roles) :
    Local registry state = GeneralNominalCenteredHeadStepBoundary.Local registry state := by
  funext demand frontier
  exact propext local_iff

theorem local_total (registry : Registry) (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier := by
  obtain ⟨frontier,localRule⟩ := GeneralNominalCenteredHeadStepBoundary.local_total registry checked state root
  exact ⟨frontier,local_iff.mpr localRule⟩

theorem local_functional (first : Local registry state root one) (last : Local registry state root two) : one = two :=
  GeneralNominalCenteredHeadStepBoundary.local_functional (local_iff.mp first) (local_iff.mp last)

end Yulang.GeneralNominalCenteredHeadWFBoundary
