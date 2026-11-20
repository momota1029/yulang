import Yulang.GeneralRebaseReceiptStampFixtures289

/-! Public readback and terminal behavior of the typed-stamped sidecar.
These theorems expose the exact original path and explicitly exclude
hypothetically modified old ledgers. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 20000000
namespace Yulang.GeneralRebaseReceiptStampedExport289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseReceiptFixture289 (request)
open GeneralRebaseReceiptWitness289 (ActualPath Witness)
open GeneralRebaseReceiptStampedProduct289 (Config Next initial project decorate project_path decorate_path decorate_project)
open GeneralRebaseReceiptStampMachine289 (Phase erase)
open GeneralRebaseReceiptCompile289 (Mark observe)
open GeneralRebaseReceiptExactLink289 (Anchored)
open GeneralRebaseReceiptScopedTrace289 (finalPhase)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedBoundary234 (Local)
open GeneralNominalVersionedEvidence231 (Evidence)
open CommonRoleOutermostResolver (Tree Resolves)

theorem erased_reachable (choice : Bool) (s : State roles) :
    (∃ phase, B4Target.Steps (Next choice) initial ⟨s,phase⟩) ↔ ActualPath choice s := by
  constructor
  · rintro ⟨phase,path⟩
    exact (GeneralRebaseReceiptAnchorProduct289.raw_paths_iff choice s).mp
      ⟨erase phase,(project_path choice path).2⟩
  · intro actual
    obtain ⟨phase,lifted⟩ := (GeneralRebaseReceiptAnchorProduct289.raw_paths_iff choice s).mpr actual
    exact ⟨_,decorate_path choice lifted⟩

theorem halt_iff (choice : Bool) {s : Config} (path : B4Target.Steps (Next choice) initial s) :
    (∀ t, ¬ Next choice s t) ↔
      (∀ t, ¬ GeneralRebaseReceiptAnchorProduct289.Next choice (project s) t) := by
  have witness := project_path choice path
  constructor
  · intro stop target move
    have newer := GeneralRebaseReceiptStampedProduct289.decorate_edge choice
      (GeneralRebaseReceiptStampedProduct289.decorate_valid choice witness.2) move
    rw [decorate_project choice s witness.1] at newer
    exact stop _ newer
  · intro stop target move
    have plain := (GeneralRebaseReceiptAnchorProduct289.paths_iff choice _).mp witness.2
    have past := GeneralRebaseReceiptRawProduct289.erase_path choice plain
    exact stop _ (GeneralRebaseReceiptStampedProduct289.project_edge choice past witness.1 move).2

noncomputable def finish (choice : Bool) : Config := decorate choice ⟨after choice,finalPhase choice⟩

theorem exact_terminal (choice : Bool) (s : Config) :
    (B4Target.Steps (Next choice) initial s ∧ (∀ t, ¬ Next choice s t)) ↔ s = finish choice := by
  constructor
  · rintro ⟨path,stop⟩
    have proof := project_path choice path
    have halt := (halt_iff choice path).mp stop
    have exactState := (GeneralRebaseReceiptAnchorProduct289.exact_terminals choice _).mp ⟨proof.2,halt⟩
    unfold finish
    rw [← exactState,decorate_project choice s proof.1]
  · rintro rfl
    obtain ⟨oldTrace,oldHalt⟩ := (GeneralRebaseReceiptAnchorProduct289.exact_terminals choice
      ⟨after choice,finalPhase choice⟩).mpr rfl
    have typed := decorate_path choice oldTrace
    refine ⟨typed,(halt_iff choice typed).mpr ?_⟩
    rw [GeneralRebaseReceiptStampedProduct289.project_decorate]
    exact oldHalt

theorem exact_old_diagnostic (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (halt : ∀ t, ¬ Next choice s t) (tree : Tree) :
    Resolves (Local (registry choice) s.raw) root tree ↔
      tree = GeneralRebaseReceiptGuardedReadback289.expectedTree choice :=
  GeneralRebaseReceiptAnchorExport289.same_terminal_diagnostic choice
    (project_path choice path).2 ((halt_iff choice path).mp halt) tree

theorem marked_result (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (value : Mark)
    (seen : observe root (erase s.phase) = some value) :
    Anchored (registry choice) s.raw root (child choice) (request choice) ∧ Witness choice s.raw ∧
    (∀ m, Models s.raw m → value.Holds m ∧ Evidence (registry choice) s.raw.core m root (.node 0 [.node 1 []])) ∧
    ¬ GeneralNominalState.Known s.raw.core.erased.current.context.state value.target :=
  GeneralRebaseReceiptAnchorExport289.released choice (project_path choice path).2 value seen

theorem no_hypothetical_destination :
    ¬ ∃ p, B4Target.Steps (Next true) initial ⟨GeneralRebaseRowLedger288.supplemented,p⟩ :=
  fun trace => GeneralRebaseRowLedgerStep288.no_raw_path_to_supplement ((erased_reachable true _).mp trace)

end Yulang.GeneralRebaseReceiptStampedExport289
