import Yulang.GeneralNominalCycleSupport
import Yulang.GeneralNominalCycleHalting
import Yulang.GeneralNominalCapturedChildOrigins

/-! Cycle-based local fields and partial transition fields on the same journal.
No completed SourceBoundary is constructed: general progress, observation
coverage, joint local classification and Evidence remain unfilled. -/
namespace Yulang.GeneralNominalCycleBoundary

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState

abbrev vocabulary := GeneralNominalSaturationBoundary.vocabulary

def localFields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) :=
  { GeneralNominalSaturationBoundary.localFields roles with
    RootK2 := fun _ state root => GeneralNominalCycleK2.RootK2 state.context.state root.demand
    CandidateK2 := fun registry state => GeneralNominalCycleK2.CandidateK2 registry state.context
    InspectionPending := fun registry state => GeneralNominalCycleK2.InspectionPending registry state.context }

def transitions (roles : Roles.RoleDecls) : GeneralNominalSaturationBoundary.Transitions roles where
  Step := GeneralNominalCycleSteps.Step
  Stable := GeneralNominalCycleSteps.Stable
  Generated := fun _ state => Generated state

theorem local_projection (registry : Registry) (state : State roles) (root : Occurrence roles) (frontier : CommonRoleOutermostResolver.Frontier (Occurrence roles)) :
    GeneralNominalLocalBoundary.Local (localFields roles) registry state root frontier ↔
      GeneralNominalCycleK2.Local registry state.context root frontier := by
  constructor
  · intro h
    exact GeneralNominalLocalBoundary.Local.rec (v := vocabulary roles) (b := localFields roles) (r := registry) (s := state)
      (motive := fun f _ => GeneralNominalCycleK2.Local registry state.context root f)
      (fun pending => .pending pending)
      (fun ready pending root candidate => .inspectionPending ready pending root candidate)
      (fun reason => .rejected reason)
      (fun ready one two different => .ambiguous ready one two different)
      (fun ready unique => .selected ready unique) h
  · intro h
    exact GeneralNominalLocalBoundary.Local.rec (v := GeneralNominalCandidates.vocabulary roles)
      (b := GeneralNominalCycleK2.fields roles) (r := registry) (s := state.context)
      (motive := fun f _ => GeneralNominalLocalBoundary.Local (localFields roles) registry state root f)
      (fun pending => .pending pending)
      (fun ready pending root candidate => .inspectionPending ready pending root candidate)
      (fun reason => .rejected reason)
      (fun ready one two different => .ambiguous ready one two different)
      (fun ready unique => .selected ready unique) h

theorem stepModels (roles : Roles.RoleDecls) :
    ∀ registry, (localFields roles).Checked registry → ∀ root before after,
      (transitions roles).Step registry root before after →
      ∀ model, (localFields roles).Models after model → (localFields roles).Models before model := by
  intro registry _ root before after update model valid
  exact GeneralNominalCycleSteps.step_models update model valid

theorem closure (roles : Roles.RoleDecls) :
    ∀ registry, (localFields roles).Checked registry → ∀ state root,
      (∀ after, ¬ (transitions roles).Step registry root state after) →
      (transitions roles).Stable registry state root ∧ ∀ child,
        (transitions roles).Generated registry state root child → (transitions roles).Stable registry state child := by
  intro registry _ state root halted
  exact GeneralNominalCycleSteps.halted_closure halted

theorem whereAccessible_of_readback (registry : Registry) (checked : Checked registry) (state : State roles)
    (readback : GeneralNominalCycleReadback.Readback roles registry state.context) (root : Occurrence roles) :
    Acc (CommonRoleOutermostResolver.Child (GeneralNominalLocalBoundary.Local (localFields roles) registry state)) root := by
  have accessible := GeneralNominalCycleReadback.whereAccessible checked readback root
  induction accessible with
  | intro root below ih =>
    refine Acc.intro root ?_
    rintro child ⟨key,children,selected,member⟩
    exact ih child ⟨key,children,(local_projection registry state root _).mp selected,member⟩

theorem survivor_unchanged (registry : Registry) (state : State roles) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) :
    (localFields roles).Survivor registry state root key children ↔
      GeneralNominalRecursiveCandidates.Survivor registry state.context root key children := Iff.rfl

end Yulang.GeneralNominalCycleBoundary
