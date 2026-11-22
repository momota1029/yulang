import Yulang.GeneralDeclarativeWhereReleaseFixture346
import Yulang.GeneralDeclarativeVersionedSeparation342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralDeclarativeWhereNonPoint346
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralWhereOriginSingleSource318 (oldPlan)
open GeneralWhereOriginSingleModel318 (previousLo)
open GeneralWhereOriginSingleCells318 (oldChild loOld loNow hi)
open GeneralWherePhysicalOldHead319 (before)
open GeneralWherePhysicalOldInstall319 (installed)
open GeneralWherePhysicalCurrentRead319 (plan low)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalCommit319 (final newChild physical_mixed_run)
open GeneralDeclarativeWhereBoth346 (polar paired)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenters (Site)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent Subtype)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

private theorem only {xs : List α} {x y : α} {i : Nat}
    (shape : xs = [x]) (same : xs[i]? = some y) : i = 0 ∧ y = x := by
  subst xs
  cases i with
  | zero => exact ⟨rfl,(Option.some.inj same).symm⟩
  | succ i => simp at same

/-- Genuine earlier nonpoint and later point-valued readings share one
final model. The actual stored centers are retained independently
of the two versioned addresses, in both child positions. -/
theorem old_and_new :
    ∃ (m : Assignment) (x y : Capture),
      GeneralWhereVersionInstall317.Models final m ∧
      x.lower = loOld ∧ x.center = oldChild.center 0 ∧ x.upper = hi ∧
      y.lower = loNow ∧ y.center = newChild.center 0 ∧ y.upper = hi ∧
      Subtype (m x.lower).1 (m x.center).1 ∧ Subtype (m x.center).1 (m x.upper).1 ∧
      Subtype (m y.lower).1 (m y.center).1 ∧ Subtype (m y.center).1 (m y.upper).1 ∧
      ¬ Equivalent (m x.lower).1 (m x.upper).1 ∧ Equivalent (m y.lower).1 (m y.upper).1 := by
  obtain ⟨s₀,_,s₁,fitOld,_,fitNew,_,_⟩ := physical_mixed_run
  obtain ⟨ord,site,i,x,num,lo,cent,hiName,oldLow,_,flo,fhi⟩ := paired s₀ previousLo _ fitOld
  obtain ⟨ord',site',j,y,num',lo',cent',hiName',newLow,_,glo,ghi⟩ := paired s₁ low _ fitNew
  have whereOld := only GeneralWherePhysicalCurrentPick319.old_emitted oldLow.emittedHere
  have whereNew := only GeneralWherePhysicalCommit319.emission newLow.emittedHere
  obtain ⟨_,rfl⟩ := whereOld
  obtain ⟨_,rfl⟩ := whereNew
  have zero : i = 0 := Fin.ext num
  have zero' : j = 0 := Fin.ext num'
  cases zero
  cases zero'
  have lowName : x.lower = loOld := lo
  have historicalHi : x.upper = hi := hiName
  have currentLo : y.lower = loNow := lo'.trans GeneralWherePhysicalCurrentRead319.address_lo
  have currentHi : y.upper = hi := hiName'.trans GeneralWherePhysicalCurrentRead319.address_hi
  have same := (GeneralDeclarativeVersionedSeparation342.mode_changes _ fitNew).2.2.2.2
  refine ⟨_,x,y,fitNew,lowName,cent,historicalHi,currentLo,cent',currentHi,flo,fhi,glo,ghi,?_,?_⟩
  · intro both
    rw [lowName,historicalHi] at both
    exact GeneralDeclarativeVersionedSeparation342.not_current_lower _ fitNew (eqv_trans both (eqv_symm same))
  · rw [currentLo,currentHi]
    exact same

end Yulang.GeneralDeclarativeWhereNonPoint346
