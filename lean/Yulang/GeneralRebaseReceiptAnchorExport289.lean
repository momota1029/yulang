import Yulang.GeneralRebaseReceiptAnchorProduct289

/-! Sound public facts for the explicitly scoped, exact-anchor product.
The exposed result includes an owning effect and complete actual child
occurrence, not matching allocator integers alone. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralRebaseReceiptAnchorExport289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptAnchorProduct289 (Next paths_iff raw_paths_iff exact_terminals)
open GeneralRebaseReceiptAnchorFixture289 (anchored_after)
open GeneralRebaseReceiptRawProduct289 (Config initial)
open GeneralRebaseReceiptExactLink289 (Anchored)
open GeneralRebaseReceiptPoint289 (release_exact published_models not_old_known)
open GeneralRebaseReceiptCompile289 (Mark observe actualMark)
open GeneralRebaseReceiptWitness289 (Witness witness_positive)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedMixedBoundary234 (Local)
open CommonRoleOutermostResolver (Tree Resolves)

theorem released (choice : Bool) {s : Config} (path : B4Target.Steps (Next choice) initial s)
    (mark : Mark) (pub : observe root s.phase = some mark) :
    Anchored (registry choice) s.raw root (child choice) (request choice) ∧
    Witness choice s.raw ∧
    (∀ m, Models s.raw m → mark.Holds m ∧ Evidence (registry choice) s.raw.core m root (.node 0 [.node 1 []])) ∧
    ¬ GeneralNominalState.Known s.raw.core.erased.current.context.state mark.target := by
  have plain := (paths_iff choice s).mp path
  obtain ⟨pos,rawEq,_,_⟩ := (release_exact choice plain mark).mp pub
  have outward := published_models choice plain mark pub
  have internal := not_old_known choice plain mark pub
  subst choice
  refine ⟨?_,?_,fun m valid => ⟨outward m valid,?_⟩,internal⟩
  · rw [rawEq]
    exact anchored_after true
  · rw [rawEq]
    exact witness_positive
  · rw [rawEq]
    exact GeneralRebaseRowParentEvidence287.evidence_root m (rawEq ▸ valid)

theorem same_terminal_diagnostic (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (halt : ∀ t, ¬ Next choice s t) (tree : Tree) :
    Resolves (Local (registry choice) s.raw) root tree ↔
      tree = GeneralRebaseReceiptGuardedReadback289.expectedTree choice := by
  have final := (exact_terminals choice s).mp ⟨path,halt⟩
  have guarded := (GeneralRebaseReceiptGuardedProduct289.exact_terminals choice s).mpr final
  exact GeneralRebaseReceiptGuardedReadback289.terminal_raw_diagnostic choice guarded.1 guarded.2 tree

theorem no_fabricated_destination :
    ¬ ∃ p, B4Target.Steps (Next true) initial ⟨GeneralRebaseRowLedger288.supplemented,p⟩ :=
  fun proof => GeneralRebaseRowLedgerStep288.no_raw_path_to_supplement ((raw_paths_iff true _).mp proof)

end Yulang.GeneralRebaseReceiptAnchorExport289
