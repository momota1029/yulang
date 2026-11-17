import Yulang.GeneralDictionaryVersionLoopFamilyRefines238
set_option backward.isDefEq.respectTransparency false
/-! Uniform syntactic revision and strict point-improvement guard. Semantic
raw-back and trusted-cache certification are deliberately not asserted here;
therefore this alone does not provide a mixed kernel step. -/
namespace Yulang.GeneralDictionaryVersionLoopFamilyRevision238
open GeneralDictionaryVersionLoopFamilyBase238 GeneralDictionaryVersionLoopFamilySnapshot238
open GeneralDictionaryVersionLoopFamilyRefines238
open GeneralNominalReobservationSteps
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
variable {roles : Roles.RoleDecls} (prior : GeneralNominalSaturationState.State roles)
abbrev current := {prior with context := ⟨state n allocated reserved ordinary,GeneralDictionaryVersionLoopSource237.interpretation⟩}

def revision : Revision (current n allocated reserved ordinary prior) where
 entries := (snapshot (n+1) allocated reserved ordinary).nominals
 catalogue := (snapshot (n+1) allocated reserved ordinary).catalogue
 opaqueHeads := by intro _ _ _; rfl
 domain := by
   intro slot
   change (if slot.val=3 then some (pair (n+1)) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none) = none ↔
     (if slot.val=n+4 then some (looseDescriptor n) else if slot.val=3 then some (rootDescriptor n) else
       if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none) = none
   by_cases last : slot.val=n+4
   · simp [last]
   · by_cases three : slot.val=3 <;> by_cases supported : slot.val=2 ∨ 4 ≤ slot.val <;> simp [last,three,supported]

theorem snapshot_exact : (revision n allocated reserved ordinary prior).snapshot = snapshot (n+1) allocated reserved ordinary := rfl

theorem point_closed : PointClosed (snapshot (n+1) allocated reserved ordinary) := by
 intro slot descriptor found
 change (if slot.val=3 then some (pair (n+1)) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none) = some descriptor at found
 split at found
 · cases Option.some.inj found
   intro parameter member
   rcases List.mem_cons.mp member with rfl | member
   · rfl
   · cases List.mem_singleton.mp member; rfl
 · split at found
   · cases Option.some.inj found
     intro parameter member
     cases List.mem_singleton.mp member; rfl
   · cases found

theorem improved : Improves (revision n allocated reserved ordinary prior) := by
 constructor
 · intro slot old
   obtain ⟨descriptor,found,_⟩ := old
   have nonempty : (revision n allocated reserved ordinary prior).entries slot ≠ none := by
     intro absent
     have oldAbsent := ((revision n allocated reserved ordinary prior).domain slot).mp absent
     rw [found] at oldAbsent
     cases oldAbsent
   cases next : (revision n allocated reserved ordinary prior).entries slot with
   | none => exact False.elim (nonempty next)
   | some descriptor =>
     exact ⟨descriptor,next,point_closed n allocated reserved ordinary slot descriptor next⟩
 · let last : Fin ((n+1)+4) := ⟨n+4,by omega⟩
   refine ⟨last,?_,foo (n+1),?_,?_⟩
   · rintro ⟨descriptor,found,point⟩
     have exactDescriptor : descriptor = looseDescriptor n := by
       change (if last.val=n+4 then _ else _) = some descriptor at found
       rw [ite_eq_left rfl] at found
       exact (Option.some.inj found).symm
     subst descriptor
     have bad := point (.type (original (n+1) 0,original (n+1) 1)) (List.mem_singleton_self _)
     have impossible := congrArg Fin.val bad
     change (0 : Nat) = 1 at impossible
     cases impossible
   · change (snapshot (n+1) allocated reserved ordinary).nominals last = _
     have notThree : last.val ≠ 3 := by dsimp [last]; omega
     have supported : last.val=2 ∨ 4 ≤ last.val := Or.inr (by dsimp [last]; omega)
     simp only [snapshot,notThree,supported,ite_false,ite_true]
   · intro parameter member
     cases List.mem_singleton.mp member; rfl
end Yulang.GeneralDictionaryVersionLoopFamilyRevision238
