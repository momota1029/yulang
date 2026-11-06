import Yulang.NestedValueSolver
import Yulang.RegularValueTypes

/-!
# Rigid constraint nodes as guarded recursive layers

Every nonvariable node contributes its actual constructor layer. The variable
case has a bottom sentinel and is excluded wherever rigid interpretation is
required. Record spines are finite and preserve first-field-wins lookup.

The reverse decomposition theorem constructs a parent subtype from the
solver's child and row obligations. Together with the forward theorem in
`NestedValueSolver`, it connects finite-depth recursive interpretation to the
actual saturation rules without assuming constructor distributivity.
-/

namespace Yulang.RigidValueLayers

open StructuralBase
open RegularValueTypes (Layer)
open NestedValueSolver (Node)

universe u

variable {n : Nat} {Row : Type u}

def recordLayer : List (Nat × Fin n) → Layer Row (Fin n)
  | [] => .emptyRecord
  | (label, field) :: rest => .record label field (recordLayer rest)

def rigidLayer : Node n Row → Layer Row (Fin n)
  | .var => .bottom
  | .bottom => .bottom
  | .top => .top
  | .base scalar => .base scalar
  | .pair left right => .pair left right
  | .arrow input inputRow output outputRow => .arrow input inputRow output outputRow
  | .record fields => recordLayer fields
  | .variant label payload => .variant label payload

@[simp] theorem recordLayer_eval (assignment : Fin n → Ty Row) (fields : List (Nat × Fin n)) :
    (recordLayer fields).eval assignment = NestedValueSolver.recordType assignment fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨label, field⟩ := field
      simp only [recordLayer, Layer.eval, NestedValueSolver.recordType, ih]

theorem rigidLayer_holds (assignment : Fin n → Ty Row) (node : Node n Row) :
    node.Holds assignment ((rigidLayer node).eval assignment) := by
  cases node <;> simp [rigidLayer, Layer.eval, Node.Holds]

theorem rigidLayer_eval_of_holds (assignment : Fin n → Ty Row) (node : Node n Row)
    (rigid : node ≠ .var) {actual : Ty Row} (shape : node.Holds assignment actual) :
    actual = (rigidLayer node).eval assignment := by
  cases node <;> simp_all [rigidLayer, Layer.eval, Node.Holds]

theorem lookupField_mem {fields : List (Nat × Fin n)} {label : Nat} {field : Fin n}
    (found : NestedValueSolver.lookupField label fields = some field) : (label, field) ∈ fields := by
  induction fields with
  | nil => cases found
  | cons head rest ih =>
      obtain ⟨key, value⟩ := head
      simp only [NestedValueSolver.lookupField] at found
      split at found
      · rename_i same
        have equal : value = field := Option.some.inj found
        subst key
        subst field
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih found)

theorem record_subtype (leRow : Row → Row → Prop)
    (left right : Fin n → Ty Row) (source target : List (Nat × Fin n))
    (covered : ∀ label expected, NestedValueSolver.lookupField label target = some expected →
      ∃ actual, NestedValueSolver.lookupField label source = some actual)
    (fields : ∀ label actual expected,
      NestedValueSolver.lookupField label source = some actual →
      NestedValueSolver.lookupField label target = some expected →
      Subtype leRow (left actual) (right expected)) :
    Subtype leRow (NestedValueSolver.recordType left source) (NestedValueSolver.recordType right target) := by
  apply Subtype.record (NestedValueSolver.recordType_shape left source)
    (NestedValueSolver.recordType_shape right target)
  · intro label expected found
    rw [NestedValueSolver.recordType_lookup] at found
    cases lookup : NestedValueSolver.lookupField label target with
    | none => simp [lookup] at found
    | some targetNode =>
        obtain ⟨actualNode, sourceFound⟩ := covered label targetNode lookup
        exact ⟨left actualNode, by simp [NestedValueSolver.recordType_lookup, sourceFound]⟩
  · intro label actual expected actualFound expectedFound
    rw [NestedValueSolver.recordType_lookup] at actualFound expectedFound
    cases sourceFound : NestedValueSolver.lookupField label source with
    | none => simp [sourceFound] at actualFound
    | some sourceNode =>
        cases targetFound : NestedValueSolver.lookupField label target with
        | none => simp [targetFound] at expectedFound
        | some targetNode =>
            have actualEqual : left sourceNode = actual := by simpa [sourceFound] using actualFound
            have expectedEqual : right targetNode = expected := by simpa [targetFound] using expectedFound
            simpa [← actualEqual, ← expectedEqual] using fields label sourceNode targetNode sourceFound targetFound

theorem recordLayer_eval_mono (leRow : Row → Row → Prop)
    (left right : Fin n → Ty Row) (below : ∀ index, Subtype leRow (left index) (right index))
    (fields : List (Nat × Fin n)) :
    Subtype leRow ((recordLayer fields).eval left) ((recordLayer fields).eval right) := by
  simp only [recordLayer_eval]
  apply record_subtype leRow left right fields fields
  · exact fun _ expected found => ⟨expected, found⟩
  · intro _ actual expected actualFound expectedFound
    have same : actual = expected := Option.some.inj (actualFound.symm.trans expectedFound)
    subst expected
    exact below actual

/-- Shared child references retain both subtype directions, including the
negative input of an arrow. Rows are fixed independently of those children. -/
theorem rigidLayer_eval_equivalent (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (left right : Fin n → Ty Row)
    (equivalent : ∀ index, Subtype leRow (left index) (right index) ∧ Subtype leRow (right index) (left index))
    (node : Node n Row) :
    Subtype leRow ((rigidLayer node).eval left) ((rigidLayer node).eval right) ∧
      Subtype leRow ((rigidLayer node).eval right) ((rigidLayer node).eval left) := by
  cases node with
  | var | bottom | top | base => exact ⟨.refl _, .refl _⟩
  | pair a b => exact ⟨.pair (equivalent a).1 (equivalent b).1, .pair (equivalent a).2 (equivalent b).2⟩
  | variant label payload => exact ⟨.variant (equivalent payload).1, .variant (equivalent payload).2⟩
  | arrow input inputRow output outputRow =>
      exact ⟨.arrow (equivalent input).2 (rowRefl _) (equivalent output).1 (rowRefl _),
        .arrow (equivalent input).1 (rowRefl _) (equivalent output).2 (rowRefl _)⟩
  | record fields =>
      exact ⟨recordLayer_eval_mono leRow left right (fun index => (equivalent index).1) fields,
        recordLayer_eval_mono leRow right left (fun index => (equivalent index).2) fields⟩

theorem record_inspect_complete (leRow : Row → Row → Prop) (assignment : Fin n → Ty Row)
    (source target : List (Nat × Fin n))
    (compatible : NestedValueSolver.recordCompatible source target = true)
    (children : ∀ edge ∈ NestedValueSolver.recordEdges source target, edge.Holds leRow assignment) :
    Subtype leRow (NestedValueSolver.recordType assignment source) (NestedValueSolver.recordType assignment target) := by
  apply record_subtype leRow assignment assignment source target
  · intro label expected found
    have member := lookupField_mem found
    have present := List.all_eq_true.mp compatible (label, expected) member
    cases sourceFound : NestedValueSolver.lookupField label source with
    | none => simp [sourceFound] at present
    | some actual => exact ⟨actual, rfl⟩
  · intro label actual expected actualFound expectedFound
    apply children (actual, expected)
    apply List.mem_filterMap.mpr
    exact ⟨(label, expected), lookupField_mem expectedFound,
      by simp [actualFound, expectedFound]⟩

/-- The solver's rigid decomposition is also sufficient at each finite
observation. The two nonvariable conditions exclude its wildcard cases. -/
theorem inspect_complete (leRow : Row → Row → Prop) (assignment : Fin n → Ty Row)
    (source target : Node n Row) (sourceRigid : source ≠ .var) (targetRigid : target ≠ .var)
    (requirements : NestedValueSolver.Requirements n Row)
    (found : NestedValueSolver.inspect source target = some requirements)
    (valid : requirements.Holds leRow assignment) :
    Subtype leRow ((rigidLayer source).eval assignment) ((rigidLayer target).eval assignment) := by
  cases source <;> cases target
  all_goals try exact False.elim (sourceRigid rfl)
  all_goals try exact False.elim (targetRigid rfl)
  all_goals try exact .bottom _
  all_goals try exact .top _
  all_goals try (simp [NestedValueSolver.inspect] at found)
  case base.base a b =>
    obtain ⟨rfl, _⟩ := found
    exact .refl _
  case pair.pair a b c d =>
    cases found
    exact .pair (valid.1 (a, c) (by simp)) (valid.1 (b, d) (by simp))
  case arrow.arrow a ea b eb c ec d ed =>
    cases found
    exact .arrow (valid.1 (c, a) (by simp)) (valid.2 (ec, ea) (by simp))
      (valid.1 (b, d) (by simp)) (valid.2 (eb, ed) (by simp))
  case record.record source target =>
    obtain ⟨compatible, rfl⟩ := found
    simpa only [rigidLayer, recordLayer_eval] using record_inspect_complete leRow assignment source target compatible valid.1
  case variant.variant label a label' b =>
    obtain ⟨rfl, rfl⟩ := found
    exact .variant (valid.1 (a, b) (by simp))

end Yulang.RigidValueLayers
