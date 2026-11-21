import Yulang.GeneralPartialDiagnosticRead310
import Yulang.GeneralNominalVersionedMixedResolver236

set_option backward.isDefEq.respectTransparency false
/-! Precise I-55(2) contract for a checked return. The actual trace, the halt,
and the history-aware reader's faithfulness still must come from the executor.
The theorem consumes rather than proves that it returned. -/
namespace Yulang.GeneralVersionedCheckedReturn310
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralPartialDiagnosticRead310 (Read Faithful check returned)
open CommonRoleOutermostResolver (Tree Resolves)

variable {roles : Roles.RoleDecls}

theorem exact_tree (registry : Registry) (root : Occurrence roles) (start after : State roles)
    (checked : (boundary roles).Checked registry)
    (initial : (boundary roles).Initial registry root start)
    (actual : B4Target.Steps ((boundary roles).Step registry root) start after)
    (halted : ∀ next, ¬ (boundary roles).Step registry root after next)
    (read : Read) (decode : Nat → Occurrence roles)
    (faith : Faithful read decode (B4TargetV8.Local (boundary roles) registry after))
    (fuel i : Nat) (reported : Tree) (source : decode i = root)
    (certificate : check read fuel i reported = true) :
    ∀ alternative, reported = alternative ↔ Resolves (B4TargetV8.Local (boundary roles) registry after) root alternative := by
  obtain ⟨path,_,resolved⟩ := returned (boundary roles) registry start after root actual initial halted
    read decode faith fuel i reported source certificate
  have equal := (GeneralNominalVersionedMixedResolver236.tree_exact checked path root reported).mpr resolved
  intro alternative
  rw [← equal]
  exact GeneralNominalVersionedMixedResolver236.tree_exact checked path root alternative

end Yulang.GeneralVersionedCheckedReturn310
