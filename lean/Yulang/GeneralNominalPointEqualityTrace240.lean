import Yulang.GeneralNominalPointKernel240
import Yulang.GeneralNominalVersionedMixedEqualityClosure235
namespace Yulang.GeneralNominalPointEqualityTrace240
open GeneralNominalVersionedJournal232 GeneralNominalPointKernel240
variable {roles : Roles.RoleDecls} {state after : State roles}

theorem steps (path : GeneralNominalVersionedMixedEqualityClosure235.Trace state after)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles) :
 B4Target.Steps (Step registry root) state after := by
 induction path with
 | refl => exact .refl
 | tail path one two equal novel ih =>
   exact .tail ih ⟨root,.root,.administrative (.equate root _ _ one two equal novel)⟩

theorem append (one : B4Target.Steps (Step registry root) a b)
 (two : B4Target.Steps (Step registry root) b c) : B4Target.Steps (Step registry root) a c := by
 induction two with
 | refl => exact one
 | tail _ action ih => exact .tail ih action
end Yulang.GeneralNominalPointEqualityTrace240
