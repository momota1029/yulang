import Yulang.ProducerContextual
import Yulang.RigidValueLayers

/-!
# Constructor inspection in the contextual demand model

The finite graph syntax is the existing `NestedValueSolver.Node`: unknowns,
bottom, top, bases, pairs, arrows with rows, proper record spines and variants.
Unknowns may be assigned arbitrary contextual types. Rigid payload obligations
use the same complete contextual order as their parents, including all demand
environments, role-head profiles and masks. This differs from the old presence
data model whose constructor payloads lost the outer mask information.

The existing executable inspector is retained. Its forward decomposition is
proved for this stronger observation vocabulary, including every rigid head
mismatch and first-field-wins record lookup. No solver success, solution cache
or restricted target argument is a premise.
-/

namespace Yulang.ContextualConstructorInspection

open StructuralBase
open NestedValueSolver (Node Valuation Requirements recordType lookupField)
open ProducerContextual

universe u
variable {n : Nat} {Row : Type u}

def RequirementsHolds (leRow : Row → Row → Prop) (value : Valuation n Row)
    (requirements : Requirements n Row) : Prop :=
  (∀ edge ∈ requirements.types, ProducerLe leRow (value edge.1) (value edge.2)) ∧
    ∀ row ∈ requirements.rows, leRow row.1 row.2

def InspectionHolds (leRow : Row → Row → Prop) (value : Valuation n Row) :
    Option (Requirements n Row) → Prop
  | none => False
  | some requirements => RequirementsHolds leRow value requirements

private theorem recordType_probeStep_field (leRow : Row → Row → Prop)
    (env : Environment Row) (argumentOrder : Ty Row → Ty Row → Prop)
    (value : Valuation n Row) (fields : List (Nat × Fin n))
    (label : Nat) (obs : Observation Row) :
    ProbeStep leRow env argumentOrder (recordType value fields) (.field label obs) ↔
      ∃ node, lookupField label fields = some node ∧
        ProbeStep leRow env argumentOrder (value node) obs := by
  induction fields with
  | nil => simp [recordType, lookupField, ProbeStep]
  | cons field rest ih =>
      obtain ⟨key, node⟩ := field
      by_cases same : label = key
      · simp [recordType, lookupField, ProbeStep, same]
      · simpa [recordType, lookupField, ProbeStep, same] using ih

theorem recordType_probe_field (leRow : Row → Row → Prop) (rank : Nat)
    (env : Environment Row) (value : Valuation n Row) (fields : List (Nat × Fin n))
    (label : Nat) (obs : Observation Row) :
    ProbeAt leRow rank env (recordType value fields) (.field label obs) ↔
      ∃ node, lookupField label fields = some node ∧
        ProbeAt leRow rank env (value node) obs := by
  cases rank <;> exact recordType_probeStep_field leRow env _ value fields label obs

theorem record_inspect_sound (leRow : Row → Row → Prop)
    (value : Valuation n Row) (source target : List (Nat × Fin n))
    (below : ProducerLe leRow (recordType value source) (recordType value target)) :
    NestedValueSolver.recordCompatible source target = true ∧
      ∀ edge ∈ NestedValueSolver.recordEdges source target,
        ProducerLe leRow (value edge.1) (value edge.2) := by
  have comparison := (producerLe_iff_probe _ _).mp below
  have covered : ∀ label expected, lookupField label target = some expected →
      ∃ actual, lookupField label source = some actual := by
    intro label expected found
    let env : Environment Row := ⟨fun _ => .bottom, fun _ => []⟩
    have targetProbe : ProbeAt leRow 0 env (recordType value target) (.field label .trivial) :=
      (recordType_probe_field leRow 0 env value target label .trivial).mpr
        ⟨expected, found, probeAt_trivial 0 _⟩
    obtain ⟨actual, available, _⟩ :=
      (recordType_probe_field leRow 0 env value source label .trivial).mp
        (comparison 0 env (.field label .trivial) targetProbe)
    exact ⟨actual, available⟩
  constructor
  · apply List.all_eq_true.mpr
    intro field member
    obtain ⟨label, field⟩ := field
    obtain ⟨expected, found⟩ := NestedValueSolver.lookupField_exists_of_mem member
    obtain ⟨actual, available⟩ := covered label expected found
    simp [available]
  · intro edge member
    obtain ⟨⟨label, field⟩, _, found⟩ := List.mem_filterMap.mp member
    cases leftFound : lookupField label source with
    | none => simp [leftFound] at found
    | some left =>
        cases rightFound : lookupField label target with
        | none => simp [leftFound, rightFound] at found
        | some right =>
            have equal : (left, right) = edge := by simpa [leftFound, rightFound] using found
            subst edge
            apply (producerLe_iff_probe _ _).mpr
            intro rank env obs accepted
            have targetProbe := (recordType_probe_field leRow rank env value target label obs).mpr
              ⟨right, rightFound, accepted⟩
            obtain ⟨actual, available, valid⟩ :=
              (recordType_probe_field leRow rank env value source label obs).mp
                (comparison rank env (.field label obs) targetProbe)
            have same : actual = left := Option.some.inj (available.symm.trans leftFound)
            simpa [same] using valid

private inductive RigidHead where
  | bottom | top | base (base : Inference.Base) | pair | arrow | record | variant (label : Nat) | lattice
  deriving DecidableEq

private def head : Ty Row → RigidHead
  | .bottom => .bottom
  | .top => .top
  | .base scalar => .base scalar
  | .pair _ _ => .pair
  | .arrow _ _ _ _ => .arrow
  | .emptyRecord | .record _ _ _ => .record
  | .variant label _ => .variant label
  | .union _ _ | .inter _ _ => .lattice

private def roleHead : Ty Row → ProducerContextual.Head
  | .base scalar => .base scalar
  | .pair _ _ => .pair
  | .arrow _ _ _ _ => .arrow
  | .variant label _ => .variant label
  | _ => .records

private def rigid : Ty Row → Bool
  | .union _ _ | .inter _ _ => false
  | _ => true

private theorem recordType_head (value : Valuation n Row) (fields : List (Nat × Fin n)) :
    head (recordType value fields) = .record := by
  cases fields <;> rfl

private theorem recordType_rigid (value : Valuation n Row) (fields : List (Nat × Fin n)) :
    rigid (recordType value fields) = true := by
  cases fields <;> rfl

/-- Concrete role tables separate every pair of distinct rigid heads. -/
private theorem rigid_heads (leRow : Row → Row → Prop)
    {source target : Ty Row} (sourceRigid : rigid source = true) (targetRigid : rigid target = true)
    (below : ProducerLe leRow source target) :
    head source = .bottom ∨ head target = .top ∨ head source = head target := by
  let env : Environment Row := ⟨fun _ => .bottom, fun _ => [roleHead target]⟩
  have impossible := (producerLe_iff_probe _ _).mp below 0 env .impossible
  have role := (producerLe_iff_probe _ _).mp below 0 env (.role 0)
  cases source <;> cases target <;>
    simp_all [rigid, head, roleHead, env, ProbeAt, ProbeStep]

private theorem variant_fields (leRow : Row → Row → Prop)
    {label label' : Nat} {a b : Ty Row}
    (below : ProducerLe leRow (.variant label a) (.variant label' b)) :
    label = label' ∧ ProducerLe leRow a b := by
  have heads := rigid_heads leRow rfl rfl below
  have same : label = label' := by simpa [head] using heads
  subst label'
  exact ⟨rfl, (producerLe_variant_iff label a b).mp below⟩

/-- Every obligation emitted by the executable inspector follows from the
independent contextual comparison. Variables retain arbitrary assignments. -/
theorem inspect_sound (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (value : Valuation n Row) (source target : Node n Row)
    {actualSource actualTarget : Ty Row}
    (sourceShape : source.Holds value actualSource) (targetShape : target.Holds value actualTarget)
    (below : ProducerLe leRow actualSource actualTarget) :
    InspectionHolds leRow value (NestedValueSolver.inspect source target) := by
  cases source <;> cases target
  all_goals try simp [NestedValueSolver.inspect, InspectionHolds, RequirementsHolds]
  all_goals simp only [Node.Holds] at sourceShape targetShape
  all_goals subst actualSource; subst actualTarget
  case pair.pair a b c d =>
    simpa [NestedValueSolver.inspect, InspectionHolds, RequirementsHolds] using
      (producerLe_pair_iff _ _ _ _).mp below
  case arrow.arrow a ea b eb c ec d ed =>
    have fields := (producerLe_arrow_iff (leRow := leRow) rowRefl rowTrans
      _ _ _ _ _ _ _ _).mp below
    simpa [NestedValueSolver.inspect, InspectionHolds, RequirementsHolds, and_assoc,
      and_left_comm, and_comm] using fields
  case record.record source target =>
    obtain ⟨compatible, fields⟩ := record_inspect_sound leRow value source target below
    simpa [NestedValueSolver.inspect, compatible, InspectionHolds, RequirementsHolds] using fields
  case variant.variant label a label' b =>
    obtain ⟨same, payload⟩ := variant_fields leRow below
    simpa [NestedValueSolver.inspect, same, InspectionHolds, RequirementsHolds] using payload
  all_goals
    have heads := rigid_heads leRow (by first | exact recordType_rigid value _ | rfl)
      (by first | exact recordType_rigid value _ | rfl) below
    try simp only [recordType_head] at heads
    simp only [head] at heads
    simp_all

end Yulang.ContextualConstructorInspection
