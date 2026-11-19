import Yulang.GeneralRebaseCompiledAcc277
import Yulang.GeneralRebaseCompiledEvidenceAt277
import Yulang.GeneralRebaseCompiledPublic277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27800
set_option maxHeartbeats 9900000
namespace Yulang.GeneralRebaseCompiledExecutor277
open GeneralNominalExamples (registry displayRoot displayChild state)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayExecutor276 (Phase Goal invocation localTable step run run_exact)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (compiled after)
open GeneralRebaseCompiledInstall277 (adapter_step direct_models models)
open GeneralRebaseCompiledAcc277 (adapter adapter_next exact_reached)
open GeneralRebaseCompiledEvidence277 (adapter_evidence)
open GeneralRebaseCompiledPublic277 (Public project decode Model canonical_exact)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

noncomputable def raw : Phase → State roles
 | .source => before
 | .settled => after

theorem distinct : before ≠ after := by
 intro same
 have edge := congrArg (fun (s : State roles) => s.core.erased.current.edges) same
 change [] = after.core.erased.current.edges at edge
 rw [GeneralRebaseCompiledInstall277.edges_eq,GeneralRebaseDisplayFrame276.actual_edges] at edge
 cases edge

theorem step_exact (a b : Phase) :
 (∃ key, step a key = some b) ↔ adapter.Step registry displayRoot (raw a) (raw b) := by
 cases a <;> cases b
 · constructor
   · rintro ⟨key,valid⟩
     by_cases h : key = 1 <;> simp [step,localTable,h] at valid
   · intro actual
     exact False.elim (distinct ((adapter_next _).mp actual))
 · exact ⟨fun _ => adapter_step,fun _ => ⟨1,rfl⟩⟩
 · constructor
   · rintro ⟨_,impossible⟩
     cases impossible
   · intro forbidden
     exact False.elim (GeneralRebaseCompiledStable277.halted _ forbidden)
 · constructor
   · rintro ⟨_,impossible⟩
     cases impossible
   · intro forbidden
     exact False.elim (GeneralRebaseCompiledStable277.halted _ forbidden)

theorem reachable_complete (s : State roles) (reached : B4Target.Steps (adapter.Step registry displayRoot) before s) :
    ∃ phase, raw phase = s := by
  rcases exact_reached s reached with rfl|rfl
  · exact ⟨.source,rfl⟩
  · exact ⟨.settled,rfl⟩

theorem exact_coincidence (a b : Phase) :
  adapter.Step registry displayRoot (raw a) (raw b) ↔
    GeneralNominalVersionedMixedKernel234.Step registry displayRoot
      (GeneralRebaseDisplayExecutor276.raw a) (GeneralRebaseDisplayExecutor276.raw b) :=
  (step_exact a b).symm.trans (GeneralRebaseDisplayExecutor276.exact_steps a b)

theorem same_models (phase : Phase) (m : Assignment) :
  Models (raw phase) m ↔ Models (GeneralRebaseDisplayExecutor276.raw phase) m := by
 cases phase
 · exact Iff.rfl
 · exact direct_models m

theorem exact_local (goal : Goal) :
  GeneralNominalVersionedMixedSourceBoundary234.Local registry after (invocation goal)
    (.selected (localTable goal).1 ((localTable goal).2.map invocation)) := by
 cases goal
 · exact GeneralRebaseCompiledSelection277.picked_parent
 · exact GeneralRebaseCompiledSelection277.picked_child

theorem readback (key : Nat) (phase : Phase) (data : Payload) (p : Public)
 (valid : Model p) (found : run key = some (phase,data)) :
  Models (raw phase) (decode p) ∧
  adapter.Evidence registry (raw phase) (decode p) displayRoot data := by
 obtain ⟨_,rfl,rfl⟩ := (run_exact key phase data).mp found
 have full := (canonical_exact p).mpr valid
 exact ⟨full,adapter_evidence _ full⟩

end Yulang.GeneralRebaseCompiledExecutor277
