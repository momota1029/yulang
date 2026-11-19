import Yulang.GeneralRebaseStoredStep280

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseStoredRegression280
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralRebaseDisplayStep276 (initial_source)
open GeneralRebaseCompiledInstall277 (adapter_step)
open GeneralRebaseArchiveReplay280 (strip restore)
open GeneralRebaseStoredStep280 (StoredStep)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)

theorem stage : B4Target.Steps ((boundary roles).Step registry displayRoot) before after :=
  .tail .refl adapter_step

theorem recovered : restore (strip after) = after :=
  GeneralRebaseArchiveReplay280.source_roundtrip initial_source stage

theorem raw_edge_absent : (strip after).core.erased.current.edges = [] := rfl

theorem restored_edge : (restore (strip after)).core.erased.current.edges = [(displayRoot,displayChild)] := by
  rw [recovered,GeneralRebaseFixedDisplayGraph280.actual_edge_list]

theorem one_stored_step (next : State roles) :
    StoredStep registry displayRoot (strip before) next ↔ next = strip after := by
  rw [GeneralRebaseStoredStep280.step initial_source .refl]
  constructor
  · rintro ⟨other,move,rfl⟩
    rw [(GeneralRebaseCompiledAcc277.adapter_next other).mp move]
  · intro same
    exact ⟨after,adapter_step,same⟩

theorem terminal : ¬ ∃ next, StoredStep registry displayRoot (strip after) next :=
  (GeneralRebaseStoredStep280.terminal_exact initial_source stage).mpr GeneralRebaseCompiledStable277.stable_parent

theorem evidenceAt : B4SkeletonV8.EvidenceAt (boundary roles) registry (restore (strip after)) displayRoot := by
  rw [recovered]
  exact GeneralRebaseCompiledEvidenceAt277.evidenceAt

theorem payload (m : Assignment) (valid : Models (restore (strip after)) m) :
    (boundary roles).Evidence registry (restore (strip after)) m displayRoot (.node 1 [.node 3 []]) := by
  rw [recovered] at valid ⊢
  exact GeneralRebaseCompiledEvidence277.real_nonleaf m valid

theorem version239_lossless (n : Nat) :
    restore (strip (GeneralDictionaryVersionLoopIteration239.state n)) =
      GeneralDictionaryVersionLoopIteration239.state n := by
  obtain ⟨start,init,walk⟩ := (GeneralDictionaryVersionLoopIteration239.stages n).reachable
  exact GeneralRebaseArchiveReplay280.source_roundtrip init walk

theorem version240_lossless (n : Nat) :
    restore (strip (GeneralDictionaryLooseIterationIteration240.state n)) =
      GeneralDictionaryLooseIterationIteration240.state n := by
  obtain ⟨start,init,walk⟩ := (GeneralDictionaryLooseIterationIteration240.stages n).reachable
  exact GeneralRebaseArchiveReplay280.source_roundtrip
    (r := GeneralDictionaryLooseLoopSource240.sourceRegistry) init
      (GeneralNominalPointErasure240.steps_old walk)

end Yulang.GeneralRebaseStoredRegression280
