import Yulang.GeneralSourceMetadataSnapshot291

/-! Do not identify same snapshot models with exact metadata or with
reachability of a differently annotated raw state. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralSourceMetadataSnapshotFixture291
open GeneralSourceMetadataRows291 (Source constructors interpretation)
open GeneralSourceMetadataSnapshot291 (attempt attempt_exact attempt_identity check)
open GeneralSourceMetadataFixture291 (source source_constructors source_interpretation)
open GeneralRebaseRowChildSource287 (raw ctx registry)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralObservedMetadataGate290 (context)
open GeneralNominalVersionedJournal232 (State)

theorem initial_exact : attempt raw source = some ctx :=
  attempt_identity ctx source source_constructors source_interpretation

theorem actual_identified (choice : Bool) {s : State GeneralRebaseRowChildSource287.roles}
    (path : ActualPath choice s) : attempt (context s).state source = some (context s) := by
  have equality := GeneralObservedMetadataActual290.actual_tables choice path
  exact attempt_identity _ source (source_constructors.trans equality.1.symm)
    (source_interpretation.trans equality.2.symm)

abbrev outside : Source := { source with rows := ⟨8,none,.unclassified⟩ :: source.rows }

abbrev removeRecorded : Source :=
  { source with rows := [⟨6,none,.unclassified⟩] ++ source.rows.filter (fun r => r.key != 6) }

theorem outside_fits : check raw outside = true := by decide +kernel

theorem observed_missing_rejected : attempt raw removeRecorded = none := by
  have reject : check raw removeRecorded ≠ true := by decide +kernel
  unfold attempt
  rw [dite_eq_right reject]

theorem same_models_not_full_metadata :
    ∃ view, attempt raw outside = some view ∧
      (∀ m, GeneralNominalState.Models view.state m ↔ GeneralNominalState.Models raw m) ∧
      ¬ GeneralNominalCandidates.Metadata (registry true) view := by
  let fits := (GeneralSourceMetadataSnapshot291.check_exact raw outside).mp outside_fits
  let view := GeneralSourceMetadataSnapshot291.context raw outside fits
  refine ⟨view,?_,GeneralSourceMetadataSnapshot291.model_preserved raw outside fits,?_⟩
  · unfold attempt
    rw [dite_eq_left outside_fits]
  · intro global
    have lost := congrFun global.1 8
    change some ⟨[],8⟩ = (none : Option GeneralDeclarationPatterns.Constructor) at lost
    cases lost

end Yulang.GeneralSourceMetadataSnapshotFixture291
