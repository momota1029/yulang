import Yulang.GeneralDeclarativeVersionedChildView342
import Yulang.GeneralWhereOriginSupport318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeVersionedEndpointOnly342
open GeneralDeclarativeVersionedChildView342 (basis lower upper actual arg done range)
open GeneralWherePhysicalCommit319 (final)
open GeneralWherePhysicalActive319 (active)
open GeneralWhereOriginSingleCells318 (loNow hi)
open GeneralWhereOriginSingleModel318 (presentLo previousHi)
open GeneralWherePhysicalEvidence319 (recorded)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeOrigins321 (Supported restriction backed_iff from_completed)
open GeneralDeclarativeTaggedSources340 (BoundsRead Read)
open GeneralDeclarativeTaggedWhole340 (fullState copied existing_head)
open GeneralDeclarativeTaggedPatch340 (captured)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeStableReads329 (One)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDictionaryJournalRefinement228Source (root interpretation)
open GeneralLiveCompoundRegistry316 (leaf)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalIdentities (Origin source)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralWhereOriginDelta318 (High)

noncomputable abbrev view : State := ⟨basis.normal,[lower,upper]⟩

noncomputable def sourceView : Supported view done :=
  ⟨fun row provenance => row ∈ view.equations ∧ provenance = .output root.identity,And.left⟩

theorem belongs (row : Equation) (r : row ∈ view.equations) :
    row ∈ (restriction sourceView).equations :=
  from_completed sourceView ⟨r,rfl⟩ ⟨rfl,recorded⟩

theorem mid_low_key : ∃ key : Origin, key.2.2.1 = 9 ∧ mid = source active.seed key := by
  exact ⟨GeneralNominalAllocation.origin root.identity declaration.id 9 0 0,rfl,rfl⟩

theorem not_center (nameHigh : High active n) : n ≠ mid := by
  obtain ⟨left,mode,eq⟩ := nameHigh
  obtain ⟨right,purpose,here⟩ := mid_low_key
  rw [eq,here]
  exact GeneralVersionedHighOrigins315.distinct (by omega) active.seed

theorem no_center_row : actual ∉ view.equations := by
  intro use
  have l : loNow ≠ mid := not_center (presentLo.high (t := active) rfl)
  have h : hi ≠ mid := not_center (previousHi.high (t := active) rfl)
  rcases List.mem_cons.mp use with first|later
  · exact l (congrArg Equation.left first).symm
  · exact h (congrArg Equation.left (List.mem_singleton.mp later)).symm

theorem no_center_source : actual ∉ (restriction sourceView).equations := by
  intro appears
  exact no_center_row (sourceView.ordinary ((backed_iff sourceView _).mp appears).choose_spec.1)

theorem endpoints : BoundsRead sourceView arg 0 (.variable 2) (.variable 2) := by
  exact ⟨range,
    ⟨_,⟨loNow,alias_refl _,belongs lower List.mem_cons_self⟩,rfl⟩,
    ⟨_,⟨hi,alias_refl _,belongs upper (List.mem_cons_of_mem _ List.mem_cons_self)⟩,rfl⟩⟩

noncomputable abbrev prepared :=
  fullState view arg 0 (.variable 2) (.variable 2) (journalSources final) (.variable 0)

noncomputable abbrev span := captured view arg 0 (.variable 2) (.variable 2) (journalSources final)

theorem no_center_observation :
    Retains view prepared (journalSources final) ∧
    One prepared sourceRegistry.constructors interpretation arg (.variant 0 (.var 0)) [(0,span)] ∧
    Bounds prepared span := by
  obtain ⟨lift,matchHead,bounds⟩ :=
    existing_head (p := sourceView) (pat := .variant 0 (.var 0))
      (c := sourceRegistry.constructors) (i := interpretation)
      (payload := .var 0) (code := .variable 0) (names := [0]) endpoints (journalSources final) rfl rfl rfl
  exact ⟨lift,matchHead,bounds _ List.mem_cons_self⟩

/-- Physical endpoint support suffices even when the ordinary centre
row is withheld. The projection is model-conservative on the
complete versioned journal footprint; the new ordinary center
fact is not independently relabelled as source support. -/
theorem preserve_current (m : Assignment) (valid : GeneralWhereVersionInstall317.Models final m) :
    ∃ n, Models prepared n ∧ GeneralWhereVersionInstall317.Models final n ∧
      ∀ id ∈ journalSources final, n id = m id := by
  have original := GeneralDeclarativeVersionedChildView342.in_every_model m valid
  have reduce : GeneralDeclarativeGrowth327.Extends view basis :=
    ⟨fun _ h => h,fun _ h => h,fun e where_ => by
      rcases List.mem_cons.mp where_ with rfl|endOf
      · exact List.mem_cons_self
      · cases List.mem_singleton.mp endOf
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have projected := GeneralDeclarativeGrowth327.restrict reduce m original
  obtain ⟨n,ready,same⟩ := no_center_observation.1.lifts m projected
  have kept id atId := same id (List.mem_append_right _ atId)
  exact ⟨n,ready,(journal_models final (fun id h => kept id h)).mpr valid,kept⟩

end Yulang.GeneralDeclarativeVersionedEndpointOnly342
