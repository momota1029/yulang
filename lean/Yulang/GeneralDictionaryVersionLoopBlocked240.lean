import Yulang.GeneralNominalPointRevision240
import Yulang.GeneralDictionaryVersionLoopFamilyRevision238
set_option backward.isDefEq.respectTransparency false
/-! I45 blocks the literal descriptor retarget used by the old 239 loop.
This rejects that revision for every index, not all possible infinite traces. -/
namespace Yulang.GeneralDictionaryVersionLoopBlocked240
open GeneralDictionaryVersionLoopFamilyBase238
open GeneralDictionaryVersionLoopFamilyRefines238
open GeneralDictionaryVersionLoopFamilyRevision238
open GeneralNominalReobservationSteps
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
variable {roles : Roles.RoleDecls} (prior : GeneralNominalSaturationState.State roles)

theorem root_point : PointDescriptor (rootDescriptor n) := by
 intro parameter member
 rcases List.mem_cons.mp member with rfl | member
 · rfl
 · cases List.mem_singleton.mp member; rfl

theorem anchor_changed : embed n (anchor n) ≠ anchor (n+1) := by
 intro same
 have values := congrArg Fin.val same
 change (if n=0 then 2 else n+3) = (if n+1=0 then 2 else n+1+3) at values
 split at values <;> simp_all <;> omega

theorem blocked : ¬ GeneralNominalPointRevision240.Preserves
 (revision n allocated reserved ordinary prior) := by
 intro preserved
 have old : (current n allocated reserved ordinary prior).context.state.nominals
     (original (n+1) 3) = some (rootDescriptor n) := by
   change (if (3 : Nat)=n+4 then some (looseDescriptor n) else some (rootDescriptor n)) = _
   rw [ite_eq_right (by omega)]
 have retained := preserved (original (n+1) 3) (rootDescriptor n) old (root_point n)
 change some (pair (n+1)) = some (rootDescriptor n) at retained
 have descriptors := Option.some.inj retained
 have parameters := congrArg GeneralNominalState.Descriptor.arguments descriptors
 have anchors : anchor (n+1) = embed n (anchor n) := by
   simpa [pair,rootDescriptor,GeneralNominalRefinements.renameDescriptor,GeneralNominalRefinements.renameParameter] using parameters
 exact anchor_changed n anchors.symm
end Yulang.GeneralDictionaryVersionLoopBlocked240
