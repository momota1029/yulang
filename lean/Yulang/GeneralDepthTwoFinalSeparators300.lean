import Yulang.GeneralDepthTwoFinalNodes300
import Yulang.GeneralDepthTwoCenters300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDepthTwoFinalSeparators300
open GeneralGeneratedNestedSource299
open GeneralDepthTwoSecondInstall300 (final)
open GeneralDepthTwoFinalNodes300 (known_slots)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedTerminalStable234 (HeadlessUnknown EqualityClosed)
open GeneralNominalVersionedMixedKernel234 (Equal)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_refl)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalRecursiveInspection (Test)

def patch (outside : Nat → Ty) : Assignment := fun i =>
  if i ≤ 2 then model i else (outside i,Common.rowEmpty)

theorem fixed (outside : Nat → Ty) (i : Nat) (small : i ≤ 2) : patch outside i = model i :=
  ite_eq_left small

theorem free (outside : Nat → Ty) (i : Nat) (large : 2 < i) :
    (patch outside i).1 = outside i := by
  unfold patch
  rw [ite_eq_right (Nat.not_le_of_gt large)]

theorem snapshot_patched (outside : Nat → Ty) : GeneralNominalState.Models snapshot (patch outside) := by
  refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
  · intro atom member
    change atom ∈ equationAtoms (2 : Fin 3) (.base .int) at member
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · change Subtype (patch outside 2).1 (.base .int)
      rw [fixed _ _ (by decide)]; exact subtype_refl _
    · change Subtype (.base .int) (patch outside 2).1
      rw [fixed _ _ (by decide)]; exact subtype_refl _
  · intro slot term equation
    change (heads slot).equation = some term at equation
    by_cases scalar : slot = 2
    · subst slot
      have eq : (.base .int : TyTerm (Fin 3)) = term := by
        simpa [heads,GeneralSourceState.Head.equation] using equation
      subst term
      change Equivalent (patch outside 2).1 (.base .int)
      rw [fixed _ _ (by decide)]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [heads,scalar,GeneralSourceState.Head.equation] at equation
  · intro pair member
    simp only [base,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> exact subtype_refl _
  · intro slot desc found
    by_cases first : slot = 0
    · subst slot
      have eq : listDescriptor 1 = desc := Option.some.inj found
      subst desc
      refine ⟨[.inl listTy],.cons ?_ .nil,?_⟩
      · change Subtype (patch outside 1).1 listTy ∧ Subtype listTy (patch outside 1).1
        rw [fixed _ _ (by decide)]
        exact ⟨subtype_refl _,subtype_refl _⟩
      · change Equivalent (patch outside 0).1 nestedTy
        rw [fixed _ _ (by decide)]
        exact ⟨subtype_refl _,subtype_refl _⟩
    · by_cases second : slot = 1
      · subst slot
        have eq : listDescriptor 2 = desc := Option.some.inj found
        subst desc
        refine ⟨[.inl intTy],.cons ?_ .nil,?_⟩
        · change Subtype (patch outside 2).1 intTy ∧ Subtype intTy (patch outside 2).1
          rw [fixed _ _ (by decide)]
          exact ⟨subtype_refl _,subtype_refl _⟩
        · change Equivalent (patch outside 1).1 listTy
          rw [fixed _ _ (by decide)]
          exact ⟨subtype_refl _,subtype_refl _⟩
      · simp [snapshot,first,second] at found

theorem patched (outside : Nat → Ty) : Models final (patch outside) := by
  apply (GeneralDepthTwoEvidence300.final_models _).mpr
  apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
  exact ⟨snapshot_patched outside,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

theorem all_known (i : Nat) (small : i ≤ 2) :
    GeneralNominalState.Known GeneralDepthTwoTerminalPlan300.env.state i := by
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases casesI with rfl|rfl|rfl
  · exact known_slots .outer
  · exact known_slots .inner
  · exact known_slots .leaf

theorem headless : HeadlessUnknown final := by
  refine ⟨patch (fun _ => .top),patched _,?_⟩
  intro id _ unknown test held
  have large : 2 < id := by
    by_cases lower : id ≤ 2
    · exact False.elim (unknown (all_known id lower))
    · omega
  rw [free _ _ large] at held
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test held

theorem not_top (i : Nat) : ¬ Equivalent .top (model i).1 := by
  intro eq
  by_cases zero : i = 0
  · subst i
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.nominal 0 1)
      ⟨[.inl listTy],rfl,eq⟩
  · by_cases one : i = 1
    · subst i
      exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.nominal 0 1)
        ⟨[.inl intTy],rfl,eq⟩
    · exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.scalar .int)
        (by simpa [GeneralGeneratedNestedSource299.model,zero,one,Test.Holds] using eq)

def mark (id : Nat) : Nat → Ty := fun name => if name = id then .top else (model name).1

theorem isolate (a b : Nat) (large : 2 < a) (apart : a ≠ b) :
    ¬ Equivalent (patch (mark a) a).1 (patch (mark a) b).1 := by
  intro eq
  rw [free _ _ large] at eq
  have right : (patch (mark a) b).1 = (model b).1 := by
    by_cases small : b ≤ 2
    · rw [fixed _ _ small]
    · rw [free _ _ (Nat.lt_of_not_ge small)]
      exact ite_eq_right (Ne.symm apart)
  rw [right] at eq
  have top : mark a a = .top := ite_eq_left rfl
  rw [top] at eq
  exact not_top b eq

theorem equality_names (a b : Nat) (same : Equal final a b) : a = b := by
  by_cases apart : a = b
  · exact apart
  by_cases aHigh : 2 < a
  · exact False.elim (isolate a b aHigh apart (same _ (patched _)))
  by_cases bHigh : 2 < b
  · have inverse := same _ (patched (mark b))
    exact False.elim (isolate b a bHigh (Ne.symm apart) ⟨inverse.2,inverse.1⟩)
  exact GeneralDepthTwoCenters300.bounded_same (by omega) (by omega)
    (same _ GeneralDepthTwoTerminalFrame300.final_model)

theorem equality_closed : EqualityClosed final := by
  intro a b _ _ same
  cases equality_names a b same
  intro m _
  exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralDepthTwoFinalSeparators300
