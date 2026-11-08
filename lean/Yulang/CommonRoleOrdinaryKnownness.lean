import Yulang.CommonRoleAssociatedStateFlow

/-! Conservative scalar evidence from original ordinary atoms. No visibility
or chosen solver assignment is consulted. Completeness concerns explicit
paired atoms only, not arbitrary semantic entailment. -/
namespace Yulang.CommonRoleOrdinaryKnownness
open Core.PresenceGeneration (Comp TyTerm)
open PresenceNormalForm (All Atom)
open CommonRoleSettledConstraints (State)

/-- A checked syntactic source for a scalar equality. -/
def Evidence (atoms : List (Atom (Fin n))) (slot : Fin n) (base : Inference.Base) : Prop :=
  Atom.tyLe (.var slot) (.base base) ∈ atoms ∧
  Atom.tyLe (.base base) (.var slot) ∈ atoms

def upperHead (slot : Fin n) : Atom (Fin n) → Option Inference.Base
  | .tyLe (.var actual) (.base base) => if actual = slot then some base else none
  | _ => none

def lowerHead (slot : Fin n) : Atom (Fin n) → Option Inference.Base
  | .tyLe (.base base) (.var actual) => if actual = slot then some base else none
  | _ => none

theorem upper_head_exact (slot : Fin n) (atom : Atom (Fin n)) (base : Inference.Base) :
    upperHead slot atom = some base ↔ atom = .tyLe (.var slot) (.base base) := by
  cases atom with
  | rowLe _ _ => simp [upperHead]
  | tyLe left right =>
    cases left <;> cases right <;> simp [upperHead]

theorem lower_head_exact (slot : Fin n) (atom : Atom (Fin n)) (base : Inference.Base) :
    lowerHead slot atom = some base ↔ atom = .tyLe (.base base) (.var slot) := by
  cases atom with
  | rowLe _ _ => simp [lowerHead]
  | tyLe left right =>
    cases left <;> cases right <;> simp [lowerHead, and_comm]

def upper (atoms : List (Atom (Fin n))) (slot : Fin n) : List Inference.Base :=
  atoms.filterMap (upperHead slot)
def lower (atoms : List (Atom (Fin n))) (slot : Fin n) : List Inference.Base :=
  atoms.filterMap (lowerHead slot)

theorem upper_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (base : Inference.Base) :
    base ∈ upper atoms slot ↔ Atom.tyLe (.var slot) (.base base) ∈ atoms := by
  simp only [upper, List.mem_filterMap, upper_head_exact]
  constructor
  · rintro ⟨a, member, rfl⟩; exact member
  · intro member; exact ⟨_, member, rfl⟩

theorem lower_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (base : Inference.Base) :
    base ∈ lower atoms slot ↔ Atom.tyLe (.base base) (.var slot) ∈ atoms := by
  simp only [lower, List.mem_filterMap, lower_head_exact]
  constructor
  · rintro ⟨a, member, rfl⟩; exact member
  · intro member; exact ⟨_, member, rfl⟩

def candidates (atoms : List (Atom (Fin n))) (slot : Fin n) : List Inference.Base :=
  (upper atoms slot).filter fun base => (lower atoms slot).contains base

theorem candidates_exact (atoms : List (Atom (Fin n))) (slot : Fin n) (base : Inference.Base) :
    base ∈ candidates atoms slot ↔ Evidence atoms slot base := by
  simp [candidates, Evidence, upper_exact, lower_exact]

def detect (atoms : List (Atom (Fin n))) (slot : Fin n) : Option Inference.Base :=
  (candidates atoms slot).head?

theorem detect_evidence (atoms : List (Atom (Fin n))) (slot : Fin n) (base : Inference.Base)
    (detected : detect atoms slot = some base) : Evidence atoms slot base := by
  apply (candidates_exact ..).mp
  exact List.mem_of_head? detected

theorem evidence_models (atoms : List (Atom (Fin n))) (slot : Fin n) (base : Inference.Base)
    (evidence : Evidence atoms slot base) (assignment : Fin n → Comp Common.model)
    (models : All Common.model assignment atoms) :
    Common.Equivalent (assignment slot).1 (.base base) := by
  exact ⟨models _ evidence.1, models _ evidence.2⟩

theorem detect_sound (atoms : List (Atom (Fin n))) (slot : Fin n) (base : Inference.Base)
    (detected : detect atoms slot = some base) (assignment : Fin n → Comp Common.model)
    (models : All Common.model assignment atoms) :
    Common.Equivalent (assignment slot).1 (.base base) :=
  evidence_models atoms slot base (detect_evidence atoms slot base detected) assignment models

/-- The scan finds some scalar exactly when explicit paired atoms exist. -/
theorem detect_exists (atoms : List (Atom (Fin n))) (slot : Fin n) :
    (∃ base, detect atoms slot = some base) ↔ ∃ base, Evidence atoms slot base := by
  constructor
  · rintro ⟨base, found⟩; exact ⟨base, detect_evidence atoms slot base found⟩
  · rintro ⟨base, evidence⟩
    have member := (candidates_exact atoms slot base).mpr evidence
    cases h : candidates atoms slot with
    | nil => simp [h] at member
    | cons first rest => exact ⟨first, by simp [detect, h]⟩

/-- Consistency, not role uniqueness, makes recorded scalar evidence unique. -/
theorem evidence_unique (atoms : List (Atom (Fin n))) (slot : Fin n)
    (assignment : Fin n → Comp Common.model) (models : All Common.model assignment atoms)
    (first last : Inference.Base) (hf : Evidence atoms slot first) (hl : Evidence atoms slot last) :
    first = last := by
  have a := evidence_models atoms slot first hf assignment models
  have b := evidence_models atoms slot last hl assignment models
  exact (CommonRigidHeadInspection.base_iff first last).mp
    (Common.equivalent_trans (Common.equivalent_symm a) b).1

/-- Only the already-used int/str first-order codes are materialized. -/
def encode : Inference.Base → Option Roles.Term
  | .int => some (.app 0 [])
  | .str => some (.app 1 [])
  | .bool | .unit => none

def materialize (atoms : List (Atom (Fin n))) (slot : Fin n) : Option Roles.Term :=
  (detect atoms slot).bind encode

theorem encode_scalar (base : Inference.Base) (term : Roles.Term)
    (encoded : encode base = some term) :
    CommonRoleAssociatedStateFlow.scalar term = some base := by
  cases base <;> simp [encode] at encoded <;> cases encoded <;> rfl

theorem materialize_sound (atoms : List (Atom (Fin n))) (slot : Fin n) (term : Roles.Term)
    (result : materialize atoms slot = some term) (assignment : Fin n → Comp Common.model)
    (models : All Common.model assignment atoms) :
    ∃ base, CommonRoleAssociatedStateFlow.scalar term = some base ∧
      Common.Equivalent (assignment slot).1 (.base base) := by
  obtain ⟨base, detected, encoded⟩ := Option.bind_eq_some_iff.mp result
  exact ⟨base, encode_scalar base term encoded, detect_sound atoms slot base detected assignment models⟩

/-- Unknown slots are not materialized even if some role has a unique impl. -/
theorem empty_pending (slot : Fin n) : materialize [] slot = none := rfl

theorem explicit_pair_detected (slot : Fin n) (base : Inference.Base) :
    detect (CommonRoleCandidateStateFrontier.equality slot base) slot = some base := by
  simp [detect, candidates, upper, lower, upperHead, lowerHead,
    CommonRoleCandidateStateFrontier.equality]

/-- A concrete adapter to the existing checked Index declaration. The receiver
payload is recovered from ordinary evidence, not selected by impl visibility. -/
def produceIndex (s : State n) (receiver output : Fin n) : Option (State n) := do
  let payload ← materialize s.atoms receiver
  CommonRoleAssociatedStateFlow.produce
    (Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl)
    Roles.AssocExamples.requiredRoles Roles.AssocExamples.box_paterson
    ⟨Roles.AssocExamples.index (Roles.AssocExamples.box payload) Roles.Examples.int, 0, output⟩ s

theorem index_from_detected_str (s : State n) (receiver output : Fin n)
    (known : detect s.atoms receiver = some .str) :
    produceIndex s receiver output =
      some (CommonRoleCandidateStateFrontier.extend s output .str) := by
  simp only [produceIndex, materialize, known, Option.bind_some, encode]
  let q : CommonRoleAssociatedStateFlow.Request n :=
    ⟨Roles.AssocExamples.index (Roles.AssocExamples.box Roles.Examples.str)
      Roles.Examples.int, 0, output⟩
  have computed : CommonRoleAssociatedStateFlow.Computed
      (Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl)
      Roles.AssocExamples.requiredRoles Roles.AssocExamples.box_paterson q .str :=
    ⟨rfl, Roles.Examples.str, Roles.AssocExamples.box_value, rfl⟩
  have hv := (CommonRoleAssociatedStateFlow.value_exact _ _ _ q .str).mpr computed
  change CommonRoleAssociatedStateFlow.produce _ _ _ q s = _
  simp only [CommonRoleAssociatedStateFlow.produce, hv, Option.map_some]
  rfl

/-- Producing an associated equation cannot erase old contradictions. This is
state preservation, not a claim that an Option.some state is consistent. -/
theorem index_preserves (s out : State n) (receiver output : Fin n)
    (produced : produceIndex s receiver output = some out)
    (assignment : Fin n → Comp Common.model)
    (models : All Common.model assignment out.atoms) :
    All Common.model assignment s.atoms := by
  cases materialized : materialize s.atoms receiver with
  | none => simp [produceIndex, materialized] at produced
  | some payload =>
      simp only [produceIndex, materialized] at produced
      obtain ⟨head, _, equal⟩ := (CommonRoleAssociatedStateFlow.produce_exact ..).mp produced
      rw [← equal] at models
      exact ((CommonRoleCandidateStateFrontier.extend_exact ..).mp models).1

theorem index_empty_pending (receiver output : Fin n) :
    produceIndex State.empty receiver output = none := rfl

/-- Full computation from a recorded scalar equation to an actual declaration
body and then an output equation. The source of the initial equation remains
outside this bridge. -/
theorem recorded_receiver_to_associated (receiver output : Fin n) :
    produceIndex (CommonRoleCandidateStateFrontier.extend State.empty receiver .str)
      receiver output =
    some (CommonRoleCandidateStateFrontier.extend
      (CommonRoleCandidateStateFrontier.extend State.empty receiver .str) output .str) := by
  apply index_from_detected_str
  exact explicit_pair_detected receiver .str

/-- A local accepted state must pass the actual ordinary solver. None may
mean missing evidence, unsupported RHS, or inconsistency; this does not expose
language-level selected/pending/rejected classification. -/
def checkedProduceIndex (s : State n) (receiver output : Fin n) : Option (State n) := do
  let out ← produceIndex s receiver output
  if CommonRoleOpenPropagation.consistent out then some out else none

theorem checked_exact (s out : State n) (receiver output : Fin n) :
    checkedProduceIndex s receiver output = some out ↔
      produceIndex s receiver output = some out ∧ out.Models := by
  unfold checkedProduceIndex
  cases h : produceIndex s receiver output with
  | none => simp
  | some result =>
      change (if CommonRoleOpenPropagation.consistent result then some result else none) = some out ↔
        some result = some out ∧ out.Models
      by_cases consistent : CommonRoleOpenPropagation.consistent result = true
      · simp only [consistent, ↓reduceIte, Option.some.injEq]
        constructor
        · intro same; subst out
          exact ⟨rfl, (CommonRoleOpenPropagation.consistent_exact result).mp consistent⟩
        · rintro ⟨same, _⟩; exact same
      · have noModel : ¬ result.Models := by
          intro models
          exact consistent ((CommonRoleOpenPropagation.consistent_exact result).mpr models)
        simp [consistent]
        intro same
        subst out
        exact noModel

theorem checked_models (s out : State n) (receiver output : Fin n)
    (accepted : checkedProduceIndex s receiver output = some out) : out.Models :=
  ((checked_exact s out receiver output).mp accepted).2

theorem checked_preserves (s out : State n) (receiver output : Fin n)
    (accepted : checkedProduceIndex s receiver output = some out)
    (assignment : Fin n → Comp Common.model)
    (models : All Common.model assignment out.atoms) :
    All Common.model assignment s.atoms :=
  index_preserves s out receiver output ((checked_exact s out receiver output).mp accepted).1
    assignment models

/-- Contradictory original evidence cannot produce an accepted local state. -/
theorem inconsistent_not_accepted (s : State n) (receiver output : Fin n)
    (inconsistent : ¬ s.Models) : checkedProduceIndex s receiver output = none := by
  cases h : checkedProduceIndex s receiver output with
  | none => rfl
  | some out =>
      obtain ⟨assignment, models⟩ := checked_models s out receiver output h
      exact False.elim (inconsistent ⟨assignment,
        checked_preserves s out receiver output h assignment models⟩)

end Yulang.CommonRoleOrdinaryKnownness
