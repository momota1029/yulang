import Yulang.GeneralRebaseRowRefreshEvidence288

/-! A canonical completion after the refresh restores the existing
dictionary, without pretending the raw input assignment already met the
parent output constraint. All row coordinates are preserved. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18000000
namespace Yulang.GeneralRebaseRowRefreshProjection288
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowLedger288 (supplemented models_eq)
open GeneralRebaseRowParentOutput287 (replaceOutput completion_rows completion_types)
open GeneralRebaseRowChildRaw287 (complete_check before_exact)
open GeneralRebaseRowLeafWitness288 (source_exact)
open GeneralRebaseRowLeafLifetime288 (topOutput source_survives)
open GeneralRebaseRowRefreshEvidence288 (exact_payload no_source_dictionary_at_mark)
open GeneralRebaseRowPublic287 (InputView ValidView canonical matches_source input_preserved other_rows)
open GeneralRebaseRowMinimal287 (Determines)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

variable {context : GeneralNominalCandidates.Context}

theorem completion_exact (cert : Refresh supplemented context) (m : Assignment) (p : Payload) :
    Models (refresh supplemented context) (replaceOutput m) ∧
      Evidence (registry true) (refresh supplemented context).core (replaceOutput m) root p ↔
    SourceSlice (after true) m ∧ p = .node 0 [.node 1 []] := by
  rw [exact_payload cert,complete_check,source_exact]

theorem public_view_exact (cert : Refresh supplemented context) (v : InputView)
    (ambient : Nat → Common.Row) (p : Payload) :
    Models (refresh supplemented context) (canonical v ambient) ∧
      Evidence (registry true) (refresh supplemented context).core (canonical v ambient) root p ↔
    ValidView v ∧ p = .node 0 [.node 1 []] := by
  rw [show canonical v ambient = replaceOutput (GeneralRebaseRowPublic287.baseFrom v ambient) from rfl,
    completion_exact cert,source_exact]
  rfl

theorem input_gate_not_raw (cert : Refresh supplemented context)
    (known : GeneralNominalState.Known context.state 2) :
    SourceSlice (refresh supplemented context) topOutput ∧
    (∀ payload, ¬ Evidence (registry true) (refresh supplemented context).core topOutput root payload) ∧
    Models (refresh supplemented context) (replaceOutput topOutput) ∧
    Evidence (registry true) (refresh supplemented context).core (replaceOutput topOutput) root (.node 0 [.node 1 []]) := by
  have original : SourceSlice (after true) topOutput := source_survives (context := context)
  exact ⟨source_survives,no_source_dictionary_at_mark cert known root,
    (completion_exact cert topOutput _).mpr ⟨original,rfl⟩⟩

theorem exact_support (cert : Refresh supplemented context) (types rows : List Nat) :
    (Determines types rows (Models (refresh supplemented context)) ↔
      0 ∈ types ∧ 1 ∈ types ∧ 2 ∈ types ∧ 0 ∈ rows) ∧
    (Determines types rows (fun m => Models (refresh supplemented context) (replaceOutput m)) ↔
      0 ∈ types ∧ 1 ∈ types ∧ 0 ∈ rows) := by
  have same : Models (refresh supplemented context) = Models (after true) :=
    funext (fun m => propext ((refresh_models cert).trans (models_eq m)))
  rw [same]
  exact ⟨GeneralRebaseRowMinimal287.after_minimal true types rows,
    GeneralRebaseRowMinimal287.canonical_minimal true types rows⟩

theorem completed_coordinates (m : Assignment) :
    (∀ n, (replaceOutput m n).2 = (m n).2) ∧
    (∀ n, n ≠ 2 → (replaceOutput m n).1 = (m n).1) :=
  ⟨completion_rows m,completion_types m⟩

end Yulang.GeneralRebaseRowRefreshProjection288
