import Yulang.GeneralRebaseReceiptLiveEffects289
import Yulang.GeneralRebaseRowFixtureDriver287

/-! Final guarded result: finite provenance, unchanged raw diagnostics,
and the exact readback of the auxiliary mark are separate conclusions. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29300
set_option maxHeartbeats 19500000
namespace Yulang.GeneralRebaseReceiptGuardedReadback289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after effect)
open GeneralRebaseReceiptWire289 (check Offer)
open GeneralRebaseReceiptFixture289 (wire request endpoint_decision)
open GeneralRebaseReceiptWitness289 (ActualPath Witness witness_positive)
open GeneralRebaseReceiptCatalogue289 (guarded constructorKeys)
open GeneralRebaseReceiptCatalogueFixture289 (guarded_actual)
open GeneralRebaseReceiptGuardedProduct289 (Next equivalent_paths)
open GeneralRebaseReceiptRawProduct289 (Config initial)
open GeneralRebaseReceiptCompile289 (Mark actualMark observe)
open GeneralRebaseReceiptPoint289 (release_exact published_models not_old_known)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedBoundary234 (Local)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Tree Resolves)

theorem provenance (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s)
    (mark : Mark) (released : observe root s.phase = some mark) :
    let keys := constructorKeys s.raw.core.erased.current.context.state
    Witness choice s.raw ∧
    (∀ key ∈ keys, (registry choice).constructors key = s.raw.core.erased.current.context.state.constructors key) ∧
    ∃ effect : Effect roles, effect ∈ s.raw.effects ∧
      (GeneralRebaseReceiptExtract289.effectSummary effect).matches (request choice) = true ∧
      ∀ key ∈ keys, (registry choice).constructors key = effect.registry.constructors key := by
  have plain := (equivalent_paths choice s).mp path
  have rawPath := GeneralRebaseReceiptRawProduct289.erase_path choice plain
  obtain ⟨pos,rawEq,_,_⟩ := (release_exact choice plain mark).mp released
  have witness : Witness choice s.raw := by subst choice; rw [rawEq]; exact witness_positive
  have accepted : check (wire choice s.raw) (request choice) = .ready :=
    (GeneralRebaseReceiptWitness289.check_iff choice rawPath).mpr witness
  refine ⟨witness,?_⟩
  apply GeneralRebaseReceiptCatalogue289.guarded_provenance
  rw [guarded_actual choice rawPath]
  exact accepted

theorem point_sound (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (mark : Mark)
    (released : observe root s.phase = some mark) :
    (∀ m, Models s.raw m → mark.Holds m) ∧
    ¬ GeneralNominalState.Known s.raw.core.erased.current.context.state mark.target := by
  have plain := (equivalent_paths choice s).mp path
  exact ⟨published_models choice plain mark released,not_old_known choice plain mark released⟩

def expectedTree (choice : Bool) : Tree :=
  .selected 0 [if choice then .selected 1 [] else .pending]

theorem terminal_raw_diagnostic (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (halt : ∀ t, ¬ Next choice s t) (tree : Tree) :
    Resolves (Local (registry choice) s.raw) root tree ↔ tree = expectedTree choice := by
  have final := (GeneralRebaseReceiptGuardedProduct289.exact_terminals choice s).mp ⟨path,halt⟩
  rw [final]
  constructor
  · intro h
    exact GeneralRebaseRowFixtureDriver287.only_root_tree choice tree h
  · rintro rfl
    cases choice
    · exact GeneralRebaseRowLocal287.blocked_tree
    · exact GeneralRebaseRowLocal287.positive_tree

theorem original_can_never_reach_supplement :
    ¬ ∃ phase, B4Target.Steps (Next true) initial ⟨GeneralRebaseRowLedger288.supplemented,phase⟩ :=
  fun trace => GeneralRebaseRowLedgerStep288.no_raw_path_to_supplement
    ((GeneralRebaseReceiptGuardedProduct289.raw_path_iff true _).mp trace)

end Yulang.GeneralRebaseReceiptGuardedReadback289
