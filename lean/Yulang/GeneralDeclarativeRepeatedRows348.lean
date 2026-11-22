import Yulang.GeneralDeclarativeRepeatedTxn348
import Yulang.GeneralDeclarativeTxnEffects348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 43000000
namespace Yulang.GeneralDeclarativeRepeatedRows348
open GeneralWhereVersionInstall317 (before fixed Models emitted)
open GeneralWhereVersionSnapshot317 (snap context)
open GeneralWhereVersionCase317 (site occ lower upper expr)
open GeneralWhereVersionBase317 (loSlot hiSlot two source_lo source_hi source_old)
open GeneralWhereOriginDelta318 (Cell High)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralDeclarativeObservedSyntax347 (structural)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWhereLegacyCut346 (sideCell)
open GeneralDeclarativeTxnCell348 (generated_cell)
open GeneralDeclarativeTxnReceipt348 (exact_position)
open GeneralDeclarativeRepeatedTxn348 (checked)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralNominalCommonBridge (Assignment)

abbrev low := sideCell .lower
abbrev high := sideCell .upper
noncomputable abbrev loRow : Equation := ⟨lower,.variant 0 (.variable 2)⟩
noncomputable abbrev hiRow : Equation := ⟨upper,.variant 0 (.variable 2)⟩

theorem observes_lower : structural snap lower = some loRow := by
  have target : sourceSlot snap.base lower = some loSlot := (sourceSlot_exact ..).mpr source_lo
  have childName : snap.base.source two = 2 := (source_old 2).trans rfl
  unfold structural
  rw [target]
  change some (⟨lower,.variant 0 (.variable (snap.base.source two))⟩ : Equation) = _
  rw [childName]

theorem observes_upper : structural snap upper = some hiRow := by
  have target : sourceSlot snap.base upper = some hiSlot := (sourceSlot_exact ..).mpr source_hi
  have childName : snap.base.source two = 2 := (source_old 2).trans rfl
  unfold structural
  rw [target]
  change some (⟨upper,.variant 0 (.variable (snap.base.source two))⟩ : Equation) = _
  rw [childName]

private theorem here {xs : List α} {s t : α} {i : Nat}
    (shape : xs = [s]) (selected : xs[i]? = some t) : i = 0 ∧ t = s := by
  subst xs
  cases i with
  | zero => exact ⟨rfl,(Option.some.inj selected).symm⟩
  | succ i => simp at selected

/-- The experimental transaction emits both corrected rows in the
very same actual clause/child position, with exact physical and
journal receipts. The old WhereStep Local premise is not used. -/
theorem exact_at (m : Assignment) (fit : Models fixed m) :
    At before fixed rootPlan low 0 site ∧ At before fixed rootPlan high 0 site := by
  obtain ⟨i,lo,first,_⟩ := generated_cell checked low m fit
  obtain ⟨j,hi,last,_⟩ := generated_cell checked high m fit
  obtain ⟨rfl,rfl⟩ := here GeneralWhereVersionInstall317.fixture_emitted first.emittedHere
  obtain ⟨rfl,rfl⟩ := here GeneralWhereVersionInstall317.fixture_emitted last.emittedHere
  exact ⟨first,last⟩

theorem corrected_position (m : Assignment) (fit : Models fixed m) :
    fixed.mixed.core.sites[2]? = some site ∧
    fixed.mixed.core.erased.current.sites[2]? = some site.observed ∧
    (GeneralWhereVersionCompiler317.children rootPlan)[0]? = some occ := by
  have a : (emitted rootPlan)[0]? = some site := (exact_at m fit).1.emittedHere
  have actual := exact_position checked m fit a
  rw [GeneralLiveCompoundPost316.centers_after,GeneralLiveCompoundPost316.raw_sites_after] at actual
  exact actual

end Yulang.GeneralDeclarativeRepeatedRows348
