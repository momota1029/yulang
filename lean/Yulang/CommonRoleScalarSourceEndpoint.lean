import Yulang.CommonRoleDynamicIndexOccurrenceDiagnostics

/-! Scalar-preserving observations over source endpoints. Unlike the legacy
int-only carrier, all existing ordinary Base heads remain distinct. This is an
observation adapter, not a new role matcher. Paired-evidence completeness requires
an actual ordinary model; arbitrary semantic entailment is not claimed. -/
namespace Yulang.CommonRoleScalarSourceEndpoint
open CommonRoleSettledConstraints (State)
open CommonRoleSettledSyntax (Constructor)
open CommonRoleOrdinaryKnownness (Evidence detect)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleSourceIdentity (Table Slot)
open CommonRoleDynamicIndexResidualBatches

inductive Value where
  | unknown
  | scalar (base : Inference.Base)
  | wrap (constructor : Constructor) (inner : Value)
  deriving DecidableEq

inductive Endpoint (n : Nat) where
  | fixed (value : Value)
  | slot (index : Fin n)
  | wrap (constructor : Constructor) (inner : Endpoint n)

def observe (s : State n) (i : Fin n) : Value :=
  match detect s.atoms i with
  | none => .unknown
  | some b => .scalar b

def Endpoint.eval (s : State n) : Endpoint n → Value
  | .fixed value => value
  | .slot i => observe s i
  | .wrap c e => .wrap c (e.eval s)

/-- Finite independent overapproximation; source identities stay in Endpoint,
not in equality of scalar values. -/
def Endpoint.variants : Endpoint n → List Value
  | .fixed value => [value]
  | .slot _ => [.unknown, .scalar .int, .scalar .bool, .scalar .str, .scalar .unit]
  | .wrap c e => e.variants.map (.wrap c)

theorem eval_present (s : State n) (e : Endpoint n) : e.eval s ∈ e.variants := by
  induction e with
  | fixed v => simp [Endpoint.eval, Endpoint.variants]
  | slot i =>
    cases h : detect s.atoms i with
    | none => simp [Endpoint.eval, Endpoint.variants, observe, h]
    | some b => cases b <;> simp [Endpoint.eval, Endpoint.variants, observe, h]
  | wrap c e ih => exact List.mem_map.mpr ⟨_,ih,rfl⟩

/-- Independent observation meaning. Unknown is an absence of information, not
an assertion of underdetermination for arbitrary ordinary states. -/
def Meaning (a : Fin n → Comp Common.model) : Endpoint n → Value → Prop
  | .fixed v, w => w = v
  | .slot _, .unknown => True
  | .slot i, .scalar b => Common.Equivalent (a i).1 (.base b)
  | .slot _, .wrap _ _ => False
  | .wrap c e, .wrap d v => c = d ∧ Meaning a e v
  | .wrap _ _, _ => False

/-- All endpoints preserve the independent ordinary model meaning, including
nested constructors and each of the four scalar heads. -/
theorem eval_sound (s : State n) (a : Fin n → Comp Common.model)
    (models : All Common.model a s.atoms) (e : Endpoint n) :
    Meaning a e (e.eval s) := by
  induction e with
  | fixed v => rfl
  | slot i =>
    cases h : detect s.atoms i with
    | none => simp [Endpoint.eval, observe, h, Meaning]
    | some b => simpa [Endpoint.eval, observe, h, Meaning] using
        CommonRoleOrdinaryKnownness.detect_sound s.atoms i b h a models
  | wrap c e ih => exact ⟨rfl,ih⟩

/-- Exact paired-evidence readout under explicit consistency, not arbitrary
semantic completeness. The model is essential on conflicting atom lists. -/
theorem observe_exact (s : State n) (a : Fin n → Comp Common.model)
    (models : All Common.model a s.atoms) (i : Fin n) (b : Inference.Base) :
    observe s i = .scalar b ↔ Evidence s.atoms i b := by
  constructor
  · intro h
    cases hd : detect s.atoms i with
    | none => simp [observe,hd] at h
    | some c =>
      have eq : c = b := by simpa [observe,hd] using h
      subst c
      exact CommonRoleOrdinaryKnownness.detect_evidence s.atoms i b hd
  · intro h
    obtain ⟨c,hc⟩ := (CommonRoleOrdinaryKnownness.detect_exists s.atoms i).mpr ⟨b,h⟩
    have eq := CommonRoleOrdinaryKnownness.evidence_unique s.atoms i a models c b
      (CommonRoleOrdinaryKnownness.detect_evidence s.atoms i c hc) h
    subst c
    simp [observe,hc]

/-- Unsupported scalar heads are not erased: the observation has exactly the
ordinary detected Base, even when the separate term encoder has no code. -/
theorem observe_detect (s : State n) (i : Fin n) (b : Inference.Base) :
    observe s i = .scalar b ↔ detect s.atoms i = some b := by
  cases h : detect s.atoms i <;> simp [observe,h]

theorem observe_unknown (s : State n) (i : Fin n) :
    observe s i = .unknown ↔ detect s.atoms i = none := by
  cases h : detect s.atoms i <;> simp [observe,h]

/-- Scalar evidence persists under added atoms, if the later state has a model.
No restriction on source-slot aliases or atom order is imposed. -/
theorem scalar_persists (before after : State n) (i : Fin n) (b : Inference.Base)
    (included : ∀ atom ∈ before.atoms, atom ∈ after.atoms)
    (a : Fin n → Comp Common.model) (models : All Common.model a after.atoms)
    (known : observe before i = .scalar b) : observe after i = .scalar b := by
  have evidence := CommonRoleOrdinaryKnownness.detect_evidence before.atoms i b
    ((observe_detect ..).mp known)
  exact (observe_exact after a models i b).mpr ⟨included _ evidence.1,included _ evidence.2⟩

/-- Reordering or duplicating ordinary atoms cannot alter any observation when
the same atom set is consistent. -/
theorem eval_order_independent (left right : State n)
    (same : ∀ atom, atom ∈ left.atoms ↔ atom ∈ right.atoms)
    (a : Fin n → Comp Common.model) (models : All Common.model a left.atoms)
    (e : Endpoint n) : e.eval left = e.eval right := by
  have modelsRight : All Common.model a right.atoms := fun atom h => models atom ((same atom).mpr h)
  have slots (i : Fin n) : observe left i = observe right i := by
    cases hl : detect left.atoms i with
    | some b =>
      have known : observe left i = .scalar b := (observe_detect ..).mpr hl
      exact known.trans (scalar_persists left right i b (fun atom h => (same atom).mp h)
        a modelsRight known).symm
    | none =>
      cases hr : detect right.atoms i with
      | none => simp [observe,hl,hr]
      | some b =>
        have back := scalar_persists right left i b (fun atom h => (same atom).mpr h)
          a models ((observe_detect ..).mpr hr)
        simp [observe,hl] at back
  induction e with
  | fixed v => rfl
  | slot i => exact slots i
  | wrap c e ih => exact congrArg (Value.wrap c) ih

/-- Each already-supported first-order scalar term is preserved by this adapter;
no nominal or integer surrogate is used for string. -/
theorem materialize_string_iff (s : State n) (i : Fin n) :
    CommonRoleOrdinaryKnownness.materialize s.atoms i = some Roles.Examples.str ↔
      observe s i = .scalar .str := by
  rw [observe_detect]
  cases h : detect s.atoms i with
  | none => simp [CommonRoleOrdinaryKnownness.materialize,h]
  | some b => cases b <;> simp [CommonRoleOrdinaryKnownness.materialize,h,
      CommonRoleOrdinaryKnownness.encode,Roles.Examples.str]

/-- On arbitrary finite original batches, the actual incremental observation
is string exactly when all independent original source models force string.
No consistency or successful-scope premise is supplied by the caller. -/
theorem solve_string_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i : Slot table) :
    observe (solve table p updates).state i = .scalar .str ↔
      CommonRoleDynamicIndexSourceSemantics.ForcesString table
        (appendMany table p updates).seeds (appendMany table p updates).links
        (appendMany table p updates).requests i := by
  rw [observe_detect]
  change detect (CommonRoleDynamicIndexEqualitySource.output table
    (advanceMany table p updates).seeds (advanceMany table p updates).links
    (advanceMany table p updates).requests).atoms i = some .str ↔ _
  rw [CommonRoleDynamicIndexSemanticSource.detect_str_iff,
    ← CommonRoleDynamicIndexSourceSemantics.source_forces_iff]
  exact ⟨fun h a ha => h a ((advanceMany_models table updates p a).mpr ha),
    fun h a ha => h a ((advanceMany_models table updates p a).mp ha)⟩

/-- In the finite positive-string construction, absence of a scalar really is
underdetermination by two original source models. This is not asserted for an
arbitrary ordinary state. -/
theorem solve_unknown_exact (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i : Slot table) :
    observe (solve table p updates).state i = .unknown ↔
      ∃ a b : Slot table → Comp Common.model,
        Satisfies table (appendMany table p updates) a ∧
        Satisfies table (appendMany table p updates) b ∧
        ¬ Common.Equivalent (a i).1 (b i).1 := by
  rw [observe_unknown]
  change _ ↔ ∃ a b,
    CommonRoleDynamicIndexSourceSemantics.SourceModel table _ _ _ a ∧
    CommonRoleDynamicIndexSourceSemantics.SourceModel table _ _ _ b ∧ _
  rw [CommonRoleDynamicIndexSourceSemantics.source_underdetermined_iff]
  change detect (CommonRoleDynamicIndexEqualitySource.output table
    (advanceMany table p updates).seeds (advanceMany table p updates).links
    (advanceMany table p updates).requests).atoms i = none ↔ _
  rw [CommonRoleDynamicIndexSemanticSource.detect_none_iff,
    ← CommonRoleDynamicIndexSourceSemantics.source_forces_iff]
  have forces : CommonRoleDynamicIndexSourceSemantics.ForcesString table
      (advanceMany table p updates).seeds (advanceMany table p updates).links
      (advanceMany table p updates).requests i ↔
      CommonRoleDynamicIndexSourceSemantics.ForcesString table
      (appendMany table p updates).seeds (appendMany table p updates).links
      (appendMany table p updates).requests i :=
    ⟨fun h a ha => h a ((advanceMany_models table updates p a).mpr ha),
      fun h a ha => h a ((advanceMany_models table updates p a).mp ha)⟩
  exact not_congr forces

/-- The scalar-preserving readout is precisely the gate of the actual checked
Index producer, including all finite supplied update rounds. -/
theorem solve_checked_iff (table : Table) (p : Problem table)
    (updates : List (Problem table)) (i j : Slot table) :
    (∃ out, CommonRoleOrdinaryKnownness.checkedProduceIndex
      (solve table p updates).state i j = some out) ↔
      observe (solve table p updates).state i = .scalar .str := by
  exact (solve_checked_exact ..).trans (solve_string_exact ..).symm

/-- Cycle53's original occurrence diagnostics now have a lossless scalar
readout. The request membership premise retains the exact original scope. -/
theorem diagnostic_waiting_iff (table : Table) (p : Problem table)
    (updates : List (Problem table)) (r : Nat × Nat)
    (hr : r ∈ (appendMany table p updates).requests) (i j : Slot table) :
    ((i,j),true) ∈ (CommonRoleDynamicIndexOccurrenceDiagnostics.inspect table
      (solve table p updates) r).endpoints ↔
      CommonRoleSourceIdentity.source table i = r.1 ∧
      CommonRoleSourceIdentity.source table j = r.2 ∧
      observe (solve table p updates).state i = .unknown := by
  rw [CommonRoleDynamicIndexOccurrenceDiagnostics.inspect_checked table p updates r hr i j,
    solve_pending_exact, ← solve_unknown_exact]

end Yulang.CommonRoleScalarSourceEndpoint
