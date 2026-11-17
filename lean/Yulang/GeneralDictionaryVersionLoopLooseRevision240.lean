import Yulang.GeneralDictionaryVersionLoopBlocked240
set_option backward.isDefEq.respectTransparency false
/-! Counterexample-first local test only: the I45 guard allows a nonpoint
root to retarget while a different descriptor becomes point. No source path,
trusted certificate, infinite iteration or target refutation is asserted. -/
namespace Yulang.GeneralDictionaryVersionLoopLooseRevision240
open GeneralDictionaryVersionLoopFamilyBase238
open GeneralDictionaryVersionLoopFamilyRefines238
open GeneralNominalReobservationSteps

abbrev loosePair (n : Nat) (a : Fin (n+4)) : GeneralNominalState.Descriptor (n+4) :=
 ⟨5,⟨[.type,.type],5⟩,[.type (a,original n 2),.type (a,original n 2)],rfl⟩
abbrev oldRoot (n : Nat) := loosePair (n+1) (embed n (anchor n))
abbrev newRoot (n : Nat) := loosePair (n+1) (anchor (n+1))

abbrev snapshot (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat)) : GeneralNominalState.State :=
 { state n allocated reserved ordinary with
   nominals := fun slot => if slot.val=3 then some (oldRoot n) else
     (state n allocated reserved ordinary).nominals slot
   catalogue := by
     intro slot d found
     split at found
     · cases Option.some.inj found; rfl
     · exact (state n allocated reserved ordinary).catalogue slot d found
   bodies_opaque := by intro _ _ _; rfl }
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))
variable {roles : Roles.RoleDecls} (prior : GeneralNominalSaturationState.State roles)
abbrev current := {prior with context := ⟨snapshot n allocated reserved ordinary,GeneralDictionaryVersionLoopSource237.interpretation⟩}

def revision : Revision (current n allocated reserved ordinary prior) where
 entries := fun slot => if slot.val=3 then some (newRoot n) else
   (GeneralDictionaryVersionLoopFamilySnapshot238.snapshot (n+1) allocated reserved ordinary).nominals slot
 catalogue := by
   intro slot d found
   split at found
   · cases Option.some.inj found; rfl
   · exact (GeneralDictionaryVersionLoopFamilySnapshot238.snapshot (n+1) allocated reserved ordinary).catalogue slot d found
 opaqueHeads := by intro _ _ _; rfl
 domain := by
   intro slot
   change (if slot.val=3 then some (newRoot n) else if slot.val=3 then _ else if slot.val=2 ∨ 4≤slot.val then _ else none)=none ↔
     (if slot.val=3 then some (oldRoot n) else if slot.val=n+4 then _ else if slot.val=3 then _ else if slot.val=2 ∨ 4≤slot.val then _ else none)=none
   by_cases root : slot.val=3
   · simp [root]
   · by_cases last : slot.val=n+4
     · have large : 4≤slot.val := by omega
       simp [last]
     · simp [root,last]

theorem old_nonpoint (positive : 0<n) : ¬ PointDescriptor (oldRoot n) := by
 intro point
 have same := point (.type (embed n (anchor n),original (n+1) 2)) (by simp)
 have values := congrArg Fin.val same
 change (if n=0 then 2 else n+3) = 2 at values
 rw [ite_eq_right (by omega)] at values
 omega

theorem last_nonpoint : ¬ PointDescriptor (looseDescriptor n) := by
 intro point
 have same := point (.type (original (n+1) 0,original (n+1) 1)) (List.mem_singleton_self _)
 have impossible := congrArg Fin.val same
 change (0:Nat)=1 at impossible
 omega

theorem preserves (positive : 0<n) : GeneralNominalPointRevision240.Preserves (revision n allocated reserved ordinary prior) := by
 intro slot descriptor found point
 change (if slot.val=3 then some (oldRoot n) else if slot.val=n+4 then some (looseDescriptor n) else if slot.val=3 then _ else if slot.val=2 ∨ 4≤slot.val then _ else none)=some descriptor at found
 by_cases root : slot.val=3
 · rw [ite_eq_left root] at found
   cases Option.some.inj found
   exact False.elim (old_nonpoint n positive point)
 · rw [ite_eq_right root] at found
   by_cases last : slot.val=n+4
   · rw [ite_eq_left last] at found
     cases Option.some.inj found
     exact False.elim (last_nonpoint n point)
   · simp only [last,root,ite_false] at found
     change (if slot.val=3 then _ else if slot.val=3 then _ else if slot.val=2 ∨ 4≤slot.val then _ else none)=some descriptor
     simpa only [root,ite_false] using found

theorem improved (positive : 0<n) : Improves (revision n allocated reserved ordinary prior) := by
 refine ⟨?_,?_⟩
 · intro slot old
   exact GeneralNominalPointRevision240.point_retained (preserves n allocated reserved ordinary prior positive) old
 · let last : Fin ((n+1)+4) := ⟨n+4,by omega⟩
   have notRoot : last.val ≠ 3 := by dsimp [last]; omega
   refine ⟨last,?_,foo (n+1),?_,?_⟩
   · rintro ⟨descriptor,found,point⟩
     change (if last.val=3 then some (oldRoot n) else if last.val=n+4 then some (looseDescriptor n) else if last.val=3 then some (rootDescriptor n) else if last.val=2 ∨ 4≤last.val then some (foo (n+1)) else none)=some descriptor at found
     rw [ite_eq_right notRoot,ite_eq_left rfl] at found
     cases Option.some.inj found
     exact last_nonpoint n point
   · change (if last.val=3 then some (newRoot n) else if last.val=3 then some (pair (n+1)) else if last.val=2 ∨ 4≤last.val then some (foo (n+1)) else none)=_
     simp only [notRoot,ite_false,show last.val=2 ∨ 4≤last.val from Or.inr (by dsimp [last]; omega),ite_true]
   · intro parameter member
     cases List.mem_singleton.mp member; rfl

theorem root_changed : (revision n allocated reserved ordinary prior).entries (original (n+1) 3) ≠
 (current n allocated reserved ordinary prior).context.state.nominals (original (n+1) 3) := by
 intro equal
 change some (newRoot n)=some (oldRoot n) at equal
 have params := congrArg GeneralNominalState.Descriptor.arguments (Option.some.inj equal)
 have same : anchor (n+1)=embed n (anchor n) := by simpa [newRoot,oldRoot,loosePair] using params
 exact GeneralDictionaryVersionLoopBlocked240.anchor_changed n same.symm
end Yulang.GeneralDictionaryVersionLoopLooseRevision240
