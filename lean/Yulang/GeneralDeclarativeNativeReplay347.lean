import Yulang.GeneralDeclarativeNativeRoot347

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralDeclarativeNativeReplay347
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedJournalFrame236 (sources models_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeLogicalChild343 (stage capture protect output child built targets fallback)
open GeneralDeclarativeInitialModels343 (kept_stage)
open GeneralDeclarativeFreshModel343 (cap_bounds)
open GeneralDeclarativeNativeRoot347 (starting_model output_holds)
open GeneralDeclarativeFreshInputs325 (whole_input_projection)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput)
open GeneralDeclarativeEntailment320 (model_append Holds)
open GeneralWhereOriginSingleSource318 (declaration declaration_checked sourceRegistry)
open GeneralLiveCompoundRegistry316 (otherChild)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralDeclarativeFreshValues343 (exact_values)
open GeneralDeclarativeNativeRead347 (genuinely_nonpoint)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)

noncomputable abbrev keep := [0,2,4,lo,mid,hi] ++ sources after

theorem preserves {m n : Assignment} (kept : ∀ k ∈ keep, n k = m k) :
    Models after m ↔ Models after n :=
  models_iff after (fun name found => (kept name (List.mem_append_right _ found)).symm)

theorem same_model (m : Assignment) (fit : Models after m) :
    ∃ n, GeneralDeclarativeHead320.Models (output keep) n ∧ Models after n ∧
      ∀ k ∈ keep, n k = m k := by
  obtain ⟨u,early,held⟩ := kept_stage keep m (starting_model m fit)
  have transform := whole_input_projection declaration_checked
    (show otherChild ∈ declaration.requirements from List.mem_cons_self)
    GeneralDeclarativeLogicalChild343.translated (cap_bounds keep) (protect keep) u
  obtain ⟨n,valid,shared⟩ := transform.mp early
  have agree : ∀ k ∈ keep, n k = m k := by
    intro k used
    exact (shared k (List.mem_append_right _ (List.mem_append_right _ used))).trans (held k used)
  have old := (preserves agree).mp fit
  refine ⟨n,(model_append n).mpr ⟨valid,?_⟩,old,agree⟩
  intro row requested
  cases List.mem_singleton.mp requested
  exact output_holds n old

/-- The witnessed current declarative child has equal endpoint *values*
in every one of these common models, while the genuine native child
has a strict interval. Therefore not even semantic endpoint aliasing
can place the actual current emitted result at that native site. -/
theorem no_same_endpoints (n : Assignment) (native : Models after n)
    (compiled : GeneralDeclarativeHead320.Models (output keep) n) :
    ¬ (Equivalent (n lo).1 (n (GeneralDeclarativeLogicalChild343.arg keep).lower).1 ∧
      Equivalent (n hi).1 (n (GeneralDeclarativeLogicalChild343.arg keep).upper).1) := by
  rintro ⟨l,h⟩
  obtain ⟨loNow,_,hiNow⟩ := exact_values keep n compiled
  exact genuinely_nonpoint n native (eqv_trans l (eqv_trans loNow
    (eqv_symm (eqv_trans h hiNow))))

theorem verified (m : Assignment) (fit : Models after m) :
    ∃ n, GeneralDeclarativeHead320.Models (output keep) n ∧ Models after n ∧
      (∀ k ∈ keep, n k = m k) ∧
      ¬ (Equivalent (n lo).1 (n (GeneralDeclarativeLogicalChild343.arg keep).lower).1 ∧
        Equivalent (n hi).1 (n (GeneralDeclarativeLogicalChild343.arg keep).upper).1) := by
  obtain ⟨n,lowered,native,kept⟩ := same_model m fit
  exact ⟨n,lowered,native,kept,no_same_endpoints n native lowered⟩

end Yulang.GeneralDeclarativeNativeReplay347
