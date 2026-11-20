import Yulang.GeneralMixedControlBisim306

namespace Yulang.GeneralMixedControlLiveness306
open GeneralDictionaryOutputDepth252 (roles root registry)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralMixedControlAtoms306 (ReachFacts reach_facts)
open GeneralMixedControlBisim306 (Observe raw labelled unlabelled)
open GeneralMixedControlMask306
variable {s t : State roles} {len : Nat}

def empty : Mask := ⟨false,false⟩
def onlyZero : Mask := ⟨true,false⟩
def onlyOne : Mask := ⟨false,true⟩
def full : Mask := ⟨true,true⟩
def masks : List Mask := [empty,onlyZero,onlyOne,full]

theorem exhaustive (x : Mask) : x ∈ masks := by
  rcases x with ⟨zero,one⟩
  cases zero <;> cases one <;> decide

def targets (x : Mask) : List Mask := masks.filter (moves x)

theorem targets_exact (x y : Mask) : y ∈ targets x ↔ moves x y = true := by
  unfold targets
  rw [List.mem_filter]
  exact ⟨And.right,fun ok => ⟨exhaustive y,ok⟩⟩

theorem full_triggers (x : Mask) (q : Fin 2) :
    fire q x full = true ↔ get x q = false := by
  rw [fire_exact]
  have top (i : Fin 2) : get full i = true := by
    unfold GeneralMixedControlMask306.get full
    split <;> rfl
  exact ⟨fun h => h.2.1,fun h => ⟨fun i _ => top i,h,top q⟩⟩

theorem label_enabled (reach : ReachFacts s) (q : Fin 2) :
    (∃ t, Observe q s t) ↔ get (project s) q = false :=
  ⟨fun ⟨_,obs⟩ => ((fire_exact _ _ _).mp
      (GeneralMixedControlBisim306.project_observe obs)).2.1,
   fun missing => let ⟨t,obs,_⟩ := (labelled reach.basic full q).mp ((full_triggers _ q).mpr missing)
      ⟨t,obs⟩⟩

theorem raw_halts (path : ActualPath installed s len) :
    (∀ t, ¬ Step registry root s t) ↔ project s = full := by
  have v := reach_facts path
  constructor
  · intro stop
    apply Mask.ext
    · cases now : (project s).zero with
      | true => rfl
      | false =>
        obtain ⟨t,h⟩ := (label_enabled v 0).mpr now
        exact False.elim (stop t ((raw v).mpr ⟨0,h⟩))
    · cases now : (project s).one with
      | true => rfl
      | false =>
        obtain ⟨t,h⟩ := (label_enabled v 1).mpr now
        exact False.elim (stop t ((raw v).mpr ⟨1,h⟩))
  · intro top t step
    obtain ⟨q,taken⟩ := (raw v).mp step
    have bad := (label_enabled v q).mp ⟨t,taken⟩
    rw [top] at bad
    unfold GeneralMixedControlMask306.get full at bad
    split at bad <;> cases bad

theorem rank_moves (x y : Mask) (given : moves x y = true) : rank y < rank x := by
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> revert given <;> decide

theorem table :
    targets empty = [onlyZero,onlyOne,full] ∧
    targets onlyZero = [full] ∧ targets onlyOne = [full] ∧ targets full = [] := by decide

theorem target_raw_exact (path : ActualPath installed s len) :
    (project t ∈ targets (project s) → ∃ next, Step registry root s next ∧ project next = project t) ∧
      (Step registry root s t → project t ∈ targets (project s)) := by
  rw [targets_exact,unlabelled path]
  exact ⟨id,fun step => ⟨_,step,rfl⟩⟩

end Yulang.GeneralMixedControlLiveness306
