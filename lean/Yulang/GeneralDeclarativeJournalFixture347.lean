import Yulang.GeneralDeclarativeJournalRelease347
import Yulang.GeneralDeclarativeNativeRead347
import Yulang.GeneralDeclarativeCurrentOrigins343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 23000000
namespace Yulang.GeneralDeclarativeJournalFixture347
open GeneralWherePhysicalActive319 (active)
open GeneralWherePhysicalCommit319 (final newChild step)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalCurrentRead319 (plan low high reads address_lo address_hi)
open GeneralWherePhysicalFresh319 (oldTwo lowerSlot upperSlot final_slots oldTwo_id)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralDeclarativeWhereAttributed346 (literal)
open GeneralDeclarativeObservedSyntax347 (structural)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeRawCapture344 (rawCap by_mode)
open GeneralDeclarativeSubstitution320 (logical EquationRead)
open GeneralDeclarativeJournalRelease347 (release)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionInstall317 (Models)
open GeneralDeclarativeWhereEndpoint346 (At)

theorem lower_literal : literal low = (⟨loNow,.variant 0 (.variable 2)⟩ : Equation) := by
  have id : low.row.target = loNow := address_lo
  change (⟨low.row.target,.variant 0 (.variable (GeneralNominalVersionedExpressionFrame236.variableSource plan .lower 0))⟩ : Equation) = _
  rw [id,reads.1]

theorem upper_literal : literal high = (⟨hi,.variant 0 (.variable 2)⟩ : Equation) := by
  have id : high.row.target = hi := address_hi
  change (⟨high.row.target,.variant 0 (.variable (GeneralNominalVersionedExpressionFrame236.variableSource plan .upper 0))⟩ : Equation) = _
  rw [id,reads.2]

theorem lower_observed : structural active low.row.target = some (literal low) := by
  rw [lower_literal,show low.row.target = loNow from address_lo]
  unfold structural
  have atLo : GeneralDictionaryBinderLocations.sourceSlot active.base loNow = some lowerSlot := final_slots.2
  rw [atLo]
  change some (⟨loNow,.variant 0 (.variable (active.base.source oldTwo))⟩ : Equation) = _
  have atName : active.base.source oldTwo = 2 := oldTwo_id
  rw [atName]

theorem upper_observed : structural active high.row.target = some (literal high) := by
  rw [upper_literal,show high.row.target = hi from address_hi]
  unfold structural
  have atHi : GeneralDictionaryBinderLocations.sourceSlot active.base hi = some upperSlot := final_slots.1
  rw [atHi]
  change some (⟨hi,.variant 0 (.variable (active.base.source oldTwo))⟩ : Equation) = _
  have atName : active.base.source oldTwo = 2 := oldTwo_id
  rw [atName]

private theorem singleton_at {xs : List α} {a b : α} {i : Nat} (h : xs = [a])
    (someAt : xs[i]? = some b) : i = 0 ∧ b = a := by
  subst xs
  cases i with
  | zero => exact ⟨rfl,(Option.some.inj someAt).symm⟩
  | succ i => simp at someAt

/-- Both inputs are truly released by the current corrected emission
in the isolated C319 path; the upper still has its separate older
physical writer. This uses a real stored head scan, not a fixture
predicate picking an index by fiat. -/
theorem released_both (m : Assignment) (fit : Models final m) :
    release final plan 1 2 0 .lower ∧ release final plan 1 2 0 .upper := by
  obtain ⟨i,s,lo,_⟩ := GeneralDeclarativeWhereEndpoint346.from_step step low m fit
  obtain ⟨j,t,hi,_⟩ := GeneralDeclarativeWhereEndpoint346.from_step step high m fit
  have i0 := (singleton_at GeneralWherePhysicalCommit319.emission lo.emittedHere).1
  have j0 := (singleton_at GeneralWherePhysicalCommit319.emission hi.emittedHere).1
  subst i; subst j
  have count : updated.mixed.core.sites.length = 2 := by rw [GeneralWherePhysicalCurrentPick319.centers]; rfl
  have first := GeneralDeclarativeJournalRelease347.actual_release lo lower_observed
  have second := GeneralDeclarativeJournalRelease347.actual_release hi upper_observed
  rw [count] at first second
  exact ⟨first,second⟩

theorem current_not_old : ¬ release final GeneralWhereOriginSingleSource318.oldPlan 1 2 0 .lower := by
  rintro ⟨c,ord,site,_,_,now⟩
  have old := now.recorded
  change some plan = some GeneralWhereOriginSingleSource318.oldPlan at old
  have same := congrArg (fun q : GeneralNominalCenters.Plan _ => q.packet.bindings) (Option.some.inj old)
  rw [GeneralWherePhysicalCurrentRead319.bindings,GeneralWhereOriginSingleRead318.old_bindings] at same
  cases same

end Yulang.GeneralDeclarativeJournalFixture347
