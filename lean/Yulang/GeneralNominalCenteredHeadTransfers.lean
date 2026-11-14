import Yulang.GeneralNominalCenteredHeadBoundary
import Yulang.GeneralNominalCenteredAdministrativeComposition

/-! Five structural bridges reuse the unchanged operational boundary.
This is not a V6 composition or an output-effect production theorem. -/
namespace Yulang.GeneralNominalCenteredHeadTransfers
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredHeadBoundary
variable {roles : Roles.RoleDecls}

theorem progress (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    Acc (fun next current => (boundary roles).Step registry root current next) state :=
  GeneralNominalCenteredAdministrativeComposition.progress registry checked state root reachable

theorem closure (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (halted : ∀ next, ¬ (boundary roles).Step registry root state next) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalCenteredAdministrativeComposition.closure registry checked state root reachable halted

theorem stepModels (registry : Registry) (checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalCenteredAdministrativeComposition.stepModels registry checked root before after reachable step

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralNominalCenteredAdministrativeComposition.dictionaryRefl (roles := roles) dictionary

theorem initialReorders (registry other : Registry) (checked : (boundary roles).Checked registry)
    (checkedOther : (boundary roles).Checked other) (order : (boundary roles).Reorders registry other)
    (state : State roles) (root : Occurrence roles) (given : (boundary roles).Initial registry root state) :
    (boundary roles).Initial other root state :=
  GeneralNominalCenteredAdministrativeComposition.initialReorders registry other checked checkedOther order state root given

end Yulang.GeneralNominalCenteredHeadTransfers
