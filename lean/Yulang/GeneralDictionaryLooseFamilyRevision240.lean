import Yulang.GeneralNominalPointRevision240
import Yulang.GeneralDictionaryLooseFamilyRefines240
set_option backward.isDefEq.respectTransparency false
/-! Uniform syntactic revision and strict point-improvement guard. Semantic
raw-back and trusted-cache certification are deliberately not asserted here;
therefore this alone does not provide a mixed kernel step. -/
namespace Yulang.GeneralDictionaryLooseFamilyRevision240
open GeneralDictionaryLooseFamilyBase240 GeneralDictionaryLooseFamilySnapshot240
open GeneralDictionaryLooseFamilyRefines240
open GeneralNominalReobservationSteps
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
variable {roles : Roles.RoleDecls} (prior : GeneralNominalSaturationState.State roles)
abbrev current := {prior with context := ⟨state n allocated reserved ordinary,GeneralDictionaryLooseLoopSource240.interpretation⟩}

def revision : Revision (current n allocated reserved ordinary prior) where
 entries := (snapshot (n+1) allocated reserved ordinary).nominals
 catalogue := (snapshot (n+1) allocated reserved ordinary).catalogue
 opaqueHeads := by intro _ _ _; rfl
 domain := by
   intro slot
   change (if slot.val=3 then some (pair (n+1)) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none) = none ↔
     (if slot.val=n+5 then some (looseDescriptor n) else if slot.val=3 then some (rootDescriptor n) else
       if slot.val=2 ∨ 4 ≤ slot.val then some (foo (n+1)) else none) = none
   by_cases last : slot.val=n+5
   · simp [last]
   · by_cases three : slot.val=3 <;> by_cases supported : slot.val=2 ∨ 4 ≤ slot.val <;> simp [last,three,supported]

theorem snapshot_exact : (revision n allocated reserved ordinary prior).snapshot = snapshot (n+1) allocated reserved ordinary := rfl

theorem root_nonpoint : ¬ PointDescriptor (rootDescriptor n) := by
 intro point
 have same := point (.type (embed n (anchor n),original (n+1) 4)) (List.mem_cons_self)
 have values := congrArg Fin.val same
 change (if n=0 then 2 else n+4)=4 at values
 split at values <;> omega

theorem last_nonpoint : ¬ PointDescriptor (looseDescriptor n) := by
 intro point
 have same := point (.type (original (n+1) 0,original (n+1) 1)) (List.mem_singleton_self _)
 have values := congrArg Fin.val same
 change (0:Nat)=1 at values
 omega

theorem preserves : GeneralNominalPointRevision240.Preserves (revision n allocated reserved ordinary prior) := by
 intro slot descriptor found point
 change (if slot.val=n+5 then some (looseDescriptor n) else if slot.val=3 then some (rootDescriptor n) else if slot.val=2 ∨ 4≤slot.val then _ else none)=some descriptor at found
 split at found
 · cases Option.some.inj found
   exact False.elim (last_nonpoint n point)
 · rename_i notLast
   split at found
   · cases Option.some.inj found
     exact False.elim (root_nonpoint n point)
   · rename_i notRoot
     change (if slot.val=3 then _ else if slot.val=2 ∨ 4≤slot.val then _ else none)=some descriptor
     simpa only [notRoot,ite_false] using found

theorem improved : Improves (revision n allocated reserved ordinary prior) := by
 refine ⟨fun slot old => GeneralNominalPointRevision240.point_retained (preserves n allocated reserved ordinary prior) old,?_⟩
 let last : Fin ((n+1)+5) := ⟨n+5,by omega⟩
 refine ⟨last,?_,foo (n+1),?_,?_⟩
 · rintro ⟨descriptor,found,point⟩
   change (if last.val=n+5 then some (looseDescriptor n) else _)=some descriptor at found
   rw [ite_eq_left rfl] at found
   cases Option.some.inj found
   exact last_nonpoint n point
 · change (GeneralDictionaryLooseFamilySnapshot240.snapshot (n+1) allocated reserved ordinary).nominals last = _
   have notThree : last.val≠3 := by dsimp [last]; omega
   have supported : last.val=2 ∨ 4≤last.val := Or.inr (by dsimp [last]; omega)
   simp only [GeneralDictionaryLooseFamilySnapshot240.snapshot,notThree,supported,ite_false,ite_true]
 · intro parameter member
   cases List.mem_singleton.mp member; rfl
end Yulang.GeneralDictionaryLooseFamilyRevision240
