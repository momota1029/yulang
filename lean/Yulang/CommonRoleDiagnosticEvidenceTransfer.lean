import Yulang.CommonRoleDiagnosticCanonicalBoundary

/-! Executable repair for one explicit reciprocal variable edge and one direct
scalar equality. This is not a transitive closure engine or arbitrary entailment
decider. It adds a logically redundant direct pair for the existing decoder. -/
namespace Yulang.CommonRoleDiagnosticEvidenceTransfer
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)
open CommonRoleOrdinaryKnownness (Evidence)
open CommonRoleCandidateStateFrontier (extend extend_exact equality)

/-- Independent local evidence sufficient to transfer one scalar equality. -/
def Transferable (s : State n) (i j : Fin n) (base : Inference.Base) : Prop :=
  Atom.tyLe (.var i) (.var j) ∈ s.atoms ∧
  Atom.tyLe (.var j) (.var i) ∈ s.atoms ∧ Evidence s.atoms j base

def edgeTest (i j : Fin n) : Atom (Fin n) → Bool
  | .tyLe (.var a) (.var b) => decide (a = i ∧ b = j)
  | _ => false

theorem edgeTest_exact (i j : Fin n) (atom : Atom (Fin n)) :
    edgeTest i j atom = true ↔ atom = .tyLe (.var i) (.var j) := by
  cases atom with
  | rowLe _ _ => simp [edgeTest]
  | tyLe a b => cases a <;> cases b <;> simp [edgeTest]

def check (s : State n) (i j : Fin n) (base : Inference.Base) : Bool :=
  (s.atoms.any (edgeTest i j)) &&
  ((s.atoms.any (edgeTest j i)) &&
  ((CommonRoleOrdinaryKnownness.upper s.atoms j).contains base &&
   (CommonRoleOrdinaryKnownness.lower s.atoms j).contains base))

theorem check_exact (s : State n) (i j : Fin n) (base : Inference.Base) :
    check s i j base = true ↔ Transferable s i j base := by
  simp [check, Transferable, Evidence, Bool.and_eq_true, List.any_eq_true,
    edgeTest_exact, CommonRoleOrdinaryKnownness.upper_exact,
    CommonRoleOrdinaryKnownness.lower_exact]

/-- Check actual atoms, and only then append the implied direct scalar pair. -/
def normalize (s : State n) (i j : Fin n) (base : Inference.Base) : State n :=
  if check s i j base then extend s i base else s

theorem transferable_models (s : State n) (i j : Fin n) (base : Inference.Base)
    (h : Transferable s i j base) (a : Fin n → Comp Common.model)
    (models : All Common.model a s.atoms) : Common.Equivalent (a i).1 (.base base) := by
  have ij : Common.Equivalent (a i).1 (a j).1 := ⟨models _ h.1,models _ h.2.1⟩
  exact Common.equivalent_trans ij
    (CommonRoleOrdinaryKnownness.evidence_models s.atoms j base h.2.2 a models)

/-- Every assignment is preserved in both directions, including inconsistent
states. No external semantic-entailment certificate is an input to normalize. -/
theorem normalize_models (s : State n) (i j : Fin n) (base : Inference.Base)
    (a : Fin n → Comp Common.model) :
    All Common.model a (normalize s i j base).atoms ↔ All Common.model a s.atoms := by
  unfold normalize
  split
  next h =>
    rw [extend_exact]
    exact ⟨And.left,fun hs => ⟨hs,transferable_models s i j base ((check_exact ..).mp h) a hs⟩⟩
  next => exact Iff.rfl

/-- Successful evidence transfer records the exact direct pair expected by the
existing detector. This is a finite syntactic bridge, not arbitrary inference. -/
theorem normalize_evidence (s : State n) (i j : Fin n) (base : Inference.Base)
    (h : Transferable s i j base) : Evidence (normalize s i j base).atoms i base := by
  simp only [normalize, (check_exact s i j base).mpr h, ↓reduceIte]
  constructor <;> simp [extend, equality]

/-- For a consistent state, checked transfer makes its source int slot visible
to the actual existing materializer. Consistency prevents conflicting witnesses. -/
theorem normalize_materializes_int (s : State n) (i j : Fin n)
    (h : Transferable s i j .int) (a : Fin n → Comp Common.model)
    (models : All Common.model a s.atoms) :
    CommonRoleOrdinaryKnownness.materialize (normalize s i j .int).atoms i =
      some Roles.Examples.int := by
  exact CommonRoleMaterializedDomain.evidence_int_materializes _ i a
    ((normalize_models s i j .int a).mpr models) (normalize_evidence s i j .int h)

/-- Concrete repair of the equal-model-set boundary from cycle29. -/
theorem boundary_repaired :
    CommonRoleOrdinaryKnownness.materialize
      (normalize CommonRoleDiagnosticCanonicalBoundary.indirect 0 1 .int).atoms 0 =
        some Roles.Examples.int := by decide

/-- Repair changes the concrete endpoint to int without changing any model. -/
theorem boundary_repaired_endpoint :
    (CommonRoleMaterializedDomain.Endpoint.slot (0 : Fin 2)).eval
      (normalize CommonRoleDiagnosticCanonicalBoundary.indirect 0 1 .int) =
    (CommonRoleMaterializedDomain.Endpoint.slot (0 : Fin 2)).eval
      CommonRoleDiagnosticCanonicalBoundary.direct := by decide

end Yulang.CommonRoleDiagnosticEvidenceTransfer
