import Yulang.CommonRoleCheckedOrdinaryReplay
import Yulang.CommonRoleEvidenceNormalization

/-! Internally computed finite scalar evidence drives actual ordinary replay.
The executable closure follows explicit reciprocal variable edges and exposes
only their derived scalar equalities. It does not generate source declarations,
new slots, new variable edges or a general state-changing role schedule. -/
namespace Yulang.CommonRoleEvidenceReplay
open CommonRoleSettledConstraints (State)
open CommonRoleEvidenceSaturation (Fact Derived saturate)
open CommonRoleCheckedOrdinaryReplay (final)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleFrontierReplay (Replay)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All Atom)

/-- Both inequalities are built by the existing grammar-checked constructor. -/
def batch (fact : Fact n) : State n :=
  CommonRoleCandidateStateFrontier.extend State.empty fact.1 fact.2

/-- The finite job list is computed from the actual initial ordinary atoms. -/
def batches (initial : State n) : List (State n) := (saturate initial).map batch

def completed (initial : State n) : State n := final initial (batches initial)

theorem batch_models (fact : Fact n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (batch fact).atoms ↔
      Common.Equivalent (assignment fact.1).1 (.base fact.2) := by
  simpa [batch, State.empty] using
    CommonRoleCandidateStateFrontier.extend_exact State.empty fact.1 fact.2 assignment

/-- Exact preservation of each assignment, not merely equisatisfiability. -/
theorem completed_models (initial : State n) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (completed initial).atoms ↔
      All Common.model assignment initial.atoms := by
  rw [completed, CommonRoleCheckedOrdinaryReplay.final_models]
  constructor
  · exact fun pair => pair.1
  · intro models
    refine ⟨models, ?_⟩
    intro actual member
    obtain ⟨fact, present, rfl⟩ := List.mem_map.mp member
    exact (batch_models fact assignment).mpr
      (CommonRoleEvidenceSaturation.derived_models initial fact
        ((CommonRoleEvidenceSaturation.saturate_exact initial fact).mp present) assignment models)

theorem completed_models_iff (initial : State n) :
    (completed initial).Models ↔ initial.Models :=
  exists_congr fun assignment => completed_models initial assignment

/-- The real solver accepts the entire generated trace exactly when the
original ordinary state is consistent; no semantic oracle enters execution. -/
theorem validate_exact (initial : State n) :
    CommonRoleCheckedOrdinaryReplay.validate initial (batches initial) = true ↔ initial.Models := by
  rw [CommonRoleCheckedOrdinaryReplay.validate_exact]
  exact completed_models_iff initial

theorem batches_length (initial : State n) :
    (batches initial).length = (saturate initial).length := List.length_map ..

theorem batches_bounded (initial : State n) : (batches initial).length ≤ n * 4 := by
  rw [batches_length]
  exact CommonRoleEvidenceSaturation.saturate_capacity initial

/-- The existing finite engine has processed every enabled scalar fact.
This concerns its explicit seed/transfer rules, not all role-generation rules. -/
theorem evidence_stopped (initial : State n) :
    FiniteHorn.firstFresh (CommonRoleEvidenceSaturation.rules initial)
      (saturate initial) (CommonRoleEvidenceSaturation.facts n) = none :=
  CommonRoleEvidenceSaturation.saturate_stopped initial

/-- The batch trace and the established normalizer preserve the same atom
membership; their list ordering is intentionally not identified. -/
theorem completed_atoms (initial : State n) (atom : Atom (Fin n)) :
    atom ∈ (completed initial).atoms ↔
      atom ∈ (CommonRoleEvidenceNormalization.normalize initial).atoms := by
  rw [completed, CommonRoleCheckedOrdinaryReplay.final_atoms]
  simp only [List.mem_append, List.mem_flatMap, batches, List.mem_map,
    CommonRoleEvidenceNormalization.normalize, CommonRoleEvidenceNormalization.emit_atoms]
  apply or_congr_right
  constructor
  · rintro ⟨actual,⟨fact,member,rfl⟩,present⟩
    exact ⟨fact,member,present⟩
  · rintro ⟨fact,member,present⟩
    exact ⟨batch fact,⟨fact,member,rfl⟩,present⟩

/-- Exactly the independently derived scalar facts are exposed, even on an
inconsistent state. This is not completeness for all semantic entailment. -/
theorem completed_evidence (initial : State n) (slot : Fin n) (base : Inference.Base) :
    CommonRoleOrdinaryKnownness.Evidence (completed initial).atoms slot base ↔
      Derived initial (slot,base) := by
  rw [← CommonRoleEvidenceNormalization.normalize_evidence initial slot base]
  simp only [CommonRoleOrdinaryKnownness.Evidence, completed_atoms]

/-- Every derived fact becomes an actual paired equality in the final state. -/
theorem derived_exposed (initial : State n) (slot : Fin n) (base : Inference.Base)
    (derived : Derived initial (slot,base)) :
    CommonRoleOrdinaryKnownness.Evidence (completed initial).atoms slot base :=
  (completed_evidence initial slot base).mpr derived

/-- Generated scalar equalities cannot invent reciprocal variable edges. -/
theorem completed_linked (initial : State n) (i j : Fin n) :
    CommonRoleEvidenceSaturation.Linked (completed initial) i j ↔
      CommonRoleEvidenceSaturation.Linked initial i j := by
  rw [← CommonRoleEvidenceNormalization.normalize_linked initial i j]
  simp only [CommonRoleEvidenceSaturation.Linked, completed_atoms]

/-- The real final ordinary state has the same scalar derivability closure. -/
theorem completed_derived (initial : State n) (fact : Fact n) :
    Derived (completed initial) fact ↔ Derived initial fact := by
  constructor
  · intro derived
    induction derived with
    | seed evidence => exact (completed_evidence ..).mp evidence
    | transfer linked _ ih => exact .transfer ((completed_linked ..).mp linked) ih
  · intro derived
    rcases fact with ⟨i,b⟩
    exact .seed (derived_exposed initial i b derived)

/-- A second pass yields no new scalar fact, including along cycles.
This is equality of fact membership, not literal list/trace idempotence. -/
theorem completed_fixedpoint (initial : State n) (fact : Fact n) :
    fact ∈ saturate (completed initial) ↔ fact ∈ saturate initial := by
  rw [CommonRoleEvidenceSaturation.saturate_exact, completed_derived,
    CommonRoleEvidenceSaturation.saturate_exact]

/-- Under original consistency, the actual detector finds every derived base.
No arbitrary choice of a satisfying assignment is used to select that base. -/
theorem derived_detected (initial : State n) (models : initial.Models)
    (slot : Fin n) (base : Inference.Base) (derived : Derived initial (slot,base)) :
    CommonRoleOrdinaryKnownness.detect (completed initial).atoms slot = some base := by
  have evidence := derived_exposed initial slot base derived
  obtain ⟨found, detected⟩ := (CommonRoleOrdinaryKnownness.detect_exists _ slot).mpr ⟨base,evidence⟩
  obtain ⟨assignment, held⟩ := (completed_models_iff initial).mpr models
  have same := CommonRoleOrdinaryKnownness.evidence_unique _ slot assignment held found base
    (CommonRoleOrdinaryKnownness.detect_evidence _ slot found detected) evidence
  simpa only [same] using detected

/-- Declaration checking and real ordinary validation precede exposed replay. -/
def run (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) : Option (Replay n) :=
  CommonRoleCheckedOrdinaryReplay.run registry slots sources original initial (batches initial)

/-- Exact returned replay, relative to original ordinary models and the
existing independently checked declaration registry. No role success is assumed. -/
theorem run_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (output : Replay n) :
    run registry slots sources original initial = some output ↔
      initial.Models ∧ ∃ checked : CommonRoleIntervalWorkClosure.Checked registry,
        output = CommonRoleFrontierReplay.replay registry checked slots sources original initial.atoms
          ((CommonRoleCheckedOrdinaryReplay.trace initial (batches initial)).map State.atoms) := by
  rw [run,CommonRoleCheckedOrdinaryReplay.run_exact]
  change ((completed initial).Models ∧ _) ↔ _
  rw [completed_models_iff]

theorem run_none_iff (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) :
    run registry slots sources original initial = none ↔
      ¬ initial.Models ∨ ¬ CommonRoleIntervalWorkClosure.Checked registry := by
  rw [run,CommonRoleCheckedOrdinaryReplay.run_none_iff]
  change (¬ (completed initial).Models ∨ _) ↔ _
  rw [completed_models_iff]

/-- Both update count and diagnostic reconstruction bounds are computed;
there is no supplied finite batch trace, model, Chain or fuel. These counts
are not bounds on total solver time or graph construction cost. -/
theorem run_computed_bound (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (output : Replay n)
    (returned : run registry slots sources original initial = some output) :
    ∃ bound, CommonRoleStateMaterializedFrontier.workDomain registry original = some bound ∧
      output.snapshots.length = 1 + (saturate initial).length ∧
      output.snapshots.length ≤ 1 + n * 4 ∧
      output.rebuilds ≤ 1 + CommonRoleMaterializationProgress.potential original ∧
      output.visits ≤ (1 + CommonRoleMaterializationProgress.potential original) * bound.length := by
  obtain ⟨bound,hbound,hlen,hrebuild,hvisits⟩ :=
    CommonRoleCheckedOrdinaryReplay.run_computed_bound registry slots sources original
      initial (batches initial) output returned
  refine ⟨bound,hbound,?_,?_,hrebuild,hvisits⟩
  · simpa only [batches_length] using hlen
  · rw [hlen]
    exact Nat.add_le_add_left (batches_bounded initial) 1

def runGraphs (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (old : Nat → Plan (Fin n)) :=
  CommonRoleCheckedOrdinaryReplay.runGraphs registry slots sources original initial (batches initial) old

/-- Every computed ordinary update refreshes its graph, even if its diagnostic
tree was reused. Graph consistency is separate from ordinary consistency. -/
theorem run_graphs_exact (registry : List Declaration) (slots : Nat → Fin n) (sources : Sources)
    (original : Goal) (initial : State n) (output : Replay n)
    (returned : run registry slots sources original initial = some output)
    (old : Nat → Plan (Fin n)) :
    ∃ graphs, runGraphs registry slots sources original initial old = some (output,graphs) ∧
      graphs.map some =
        (initial.atoms :: (CommonRoleCheckedOrdinaryReplay.trace initial (batches initial)).map State.atoms).mapIdx
          (fun i atoms => CommonRoleStateMaterializedFrontier.run registry slots sources atoms (old i) original) :=
  CommonRoleCheckedOrdinaryReplay.run_graphs_exact registry slots sources original
    initial (batches initial) output returned old

end Yulang.CommonRoleEvidenceReplay
