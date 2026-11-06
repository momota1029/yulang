import Yulang.FiniteHorn
import Yulang.ValueBoundElimination

/-!
# Finite saturation of constructor-nested subtype constraints

Nodes retain the original simple-type constructors; arrow inputs reverse
the generated obligation and outputs preserve it. Variables have incoming
lower and outgoing upper bounds. Saturation propagates each lower/upper pair
through its variable, and decomposes the resulting rigid constructor pair.
All cached facts are pairs of nodes from the original finite graph.

The declarative meaning assigns arbitrary structural types to variable nodes
and interprets constructor nodes as their actual constructors. The preservation
and rejection theorems quantify over all such assignments. An accepted result
certifies finite closure consistency; construction of a regular recursive
principal solution is a separate theorem, not assumed here.
-/

namespace Yulang.NestedValueSolver

open StructuralBase

universe u

variable {n : Nat} {RowType : Type u}

abbrev Edge (n : Nat) := Fin n × Fin n

inductive Node (n : Nat) (RowType : Type u) where
  | var
  | bottom
  | top
  | base (base : Inference.Base)
  | pair (left right : Fin n)
  | arrow (input : Fin n) (inputRow : RowType) (output : Fin n) (outputRow : RowType)
  | record (fields : List (Nat × Fin n))
  | variant (label : Nat) (payload : Fin n)
  deriving Repr

abbrev Graph (n : Nat) (RowType : Type u) := Fin n → Node n RowType
abbrev Valuation (n : Nat) (RowType : Type u) := Fin n → Ty RowType

def lookupField (label : Nat) : List (Nat × Fin n) → Option (Fin n)
  | [] => none
  | (key, value) :: rest => if label = key then some value else lookupField label rest

def recordType (value : Valuation n RowType) : List (Nat × Fin n) → Ty RowType
  | [] => .emptyRecord
  | (label, field) :: rest => .record label (value field) (recordType value rest)

theorem recordType_shape (value : Valuation n RowType) (fields : List (Nat × Fin n)) :
    IsRecord (recordType value fields) := by
  induction fields with
  | nil => exact .empty
  | cons field rest ih => exact .field ih

theorem recordType_lookup (value : Valuation n RowType) (fields : List (Nat × Fin n))
    (label : Nat) :
    (recordType value fields).lookup label = (lookupField label fields).map value := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨key, field⟩ := field
      simp only [recordType, Ty.lookup, lookupField]
      split <;> simp_all

theorem lookupField_exists_of_mem {fields : List (Nat × Fin n)} {label : Nat} {field : Fin n}
    (member : (label, field) ∈ fields) : ∃ actual, lookupField label fields = some actual := by
  induction fields with
  | nil => cases member
  | cons head rest ih =>
      obtain ⟨key, value⟩ := head
      by_cases equal : label = key
      · exact ⟨value, by simp [lookupField, equal]⟩
      · rcases List.mem_cons.mp member with same | member
        · exact False.elim (equal (Prod.mk.inj same).1)
        · obtain ⟨actual, found⟩ := ih member
          exact ⟨actual, by simp [lookupField, equal, found]⟩

def Node.Holds (value : Valuation n RowType) (actual : Ty RowType) : Node n RowType → Prop
  | .var => True
  | .bottom => actual = .bottom
  | .top => actual = .top
  | .base scalar => actual = .base scalar
  | .pair left right => actual = .pair (value left) (value right)
  | .arrow input inputRow output outputRow =>
      actual = .arrow (value input) inputRow (value output) outputRow
  | .record fields => actual = recordType value fields
  | .variant label payload => actual = .variant label (value payload)

def Realizes (graph : Graph n RowType) (value : Valuation n RowType) : Prop :=
  ∀ node, (graph node).Holds value (value node)

def Edge.Holds (leRow : RowType → RowType → Prop) (value : Valuation n RowType)
    (edge : Edge n) : Prop := Subtype leRow (value edge.1) (value edge.2)

def Models (leRow : RowType → RowType → Prop) (graph : Graph n RowType)
    (constraints : List (Edge n)) (value : Valuation n RowType) : Prop :=
  Realizes graph value ∧ ∀ edge ∈ constraints, edge.Holds leRow value

structure Requirements (n : Nat) (RowType : Type u) where
  types : List (Edge n) := []
  rows : List (RowType × RowType) := []

def Requirements.Holds (leRow : RowType → RowType → Prop) (value : Valuation n RowType)
    (requirements : Requirements n RowType) : Prop :=
  (∀ edge ∈ requirements.types, edge.Holds leRow value) ∧
    ∀ row ∈ requirements.rows, leRow row.1 row.2

def recordCompatible (source target : List (Nat × Fin n)) : Bool :=
  target.all fun field => (lookupField field.1 source).isSome

/-- Repeated labels use their first field on both sides, as in the reference algebra. -/
def recordEdges (source target : List (Nat × Fin n)) : List (Edge n) :=
  target.filterMap fun field => do
    let left ← lookupField field.1 source
    let right ← lookupField field.1 target
    pure (left, right)

def inspect : Node n RowType → Node n RowType → Option (Requirements n RowType)
  | .var, _ | _, .var => some {}
  | .bottom, _ | _, .top => some {}
  | .base left, .base right => if left = right then some {} else none
  | .pair a b, .pair c d => some { types := [(a, c), (b, d)] }
  | .arrow a ea b eb, .arrow c ec d ed =>
      some { types := [(c, a), (b, d)], rows := [(ec, ea), (eb, ed)] }
  | .record source, .record target =>
      if recordCompatible source target then some { types := recordEdges source target } else none
  | .variant label left, .variant label' right =>
      if label = label' then some { types := [(left, right)] } else none
  | _, _ => none

def InspectionHolds (leRow : RowType → RowType → Prop) (value : Valuation n RowType) :
    Option (Requirements n RowType) → Prop
  | none => False
  | some requirements => requirements.Holds leRow value

theorem record_inspect_sound (leRow : RowType → RowType → Prop)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (value : Valuation n RowType) (source target : List (Nat × Fin n))
    (subtype : Subtype leRow (recordType value source) (recordType value target)) :
    recordCompatible source target = true ∧
      ∀ edge ∈ recordEdges source target, edge.Holds leRow value := by
  obtain ⟨fields, comparisons⟩ := ValueBoundElimination.record_subtype_fields (leRow := leRow) rowTrans
    (recordType_shape value source) (recordType_shape value target) subtype
  constructor
  · apply List.all_eq_true.mpr
    intro field member
    obtain ⟨label, field⟩ := field
    obtain ⟨expected, expectedFound⟩ := lookupField_exists_of_mem member
    obtain ⟨actual, actualFound⟩ := fields label (value expected)
      (by simp [recordType_lookup, expectedFound])
    rw [recordType_lookup] at actualFound
    cases found : lookupField label source with
    | none => simp [found] at actualFound
    | some actual => simp
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
            exact comparisons label (value left) (value right)
              (by simp [recordType_lookup, leftFound])
              (by simp [recordType_lookup, rightFound])

private inductive Head where
  | bottom | top | base (base : Inference.Base) | pair | arrow | record | variant (label : Nat) | lattice
  deriving DecidableEq

private def head : Ty RowType → Head
  | .bottom => .bottom
  | .top => .top
  | .base scalar => .base scalar
  | .pair _ _ => .pair
  | .arrow _ _ _ _ => .arrow
  | .emptyRecord | .record _ _ _ => .record
  | .variant label _ => .variant label
  | .union _ _ | .inter _ _ => .lattice

private def rigid : Ty RowType → Bool
  | .union _ _ | .inter _ _ => false
  | _ => true

private theorem record_head {type : Ty RowType} (shape : IsRecord type) : head type = .record := by
  cases shape <;> rfl

private theorem recordType_head (value : Valuation n RowType) (fields : List (Nat × Fin n)) :
    head (recordType value fields) = .record := record_head (recordType_shape value fields)

private theorem recordType_rigid (value : Valuation n RowType) (fields : List (Nat × Fin n)) :
    rigid (recordType value fields) = true := by
  cases fields <;> rfl

private theorem rigid_heads (leRow : RowType → RowType → Prop)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    {source target : Ty RowType} (sourceRigid : rigid source = true) (targetRigid : rigid target = true)
    (subtype : Subtype leRow source target) :
    head source = .bottom ∨ head target = .top ∨ head source = head target := by
  cases StructuralDecisions.Comparison.complete (leRow := leRow) rowTrans subtype with
  | refl => exact Or.inr (Or.inr rfl)
  | bottom => exact Or.inl rfl
  | top => exact Or.inr (Or.inl rfl)
  | unionElim | interLeft | interRight => cases sourceRigid
  | interIntro | unionLeft | unionRight => cases targetRigid
  | pair | arrow | variant => exact Or.inr (Or.inr rfl)
  | record sourceShape targetShape _ _ =>
      exact Or.inr (Or.inr ((record_head sourceShape).trans (record_head targetShape).symm))

private theorem pair_fields (leRow : RowType → RowType → Prop)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    {a b c d : Ty RowType} (subtype : Subtype leRow (.pair a b) (.pair c d)) :
    Subtype leRow a c ∧ Subtype leRow b d := by
  cases StructuralDecisions.Comparison.complete (leRow := leRow) rowTrans subtype with
  | refl => exact ⟨.refl _, .refl _⟩
  | pair left right => exact ⟨left.sound, right.sound⟩
  | record shape => cases shape

private theorem arrow_fields (leRow : RowType → RowType → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    {a b c d : Ty RowType} {ea eb ec ed : RowType}
    (subtype : Subtype leRow (.arrow a ea b eb) (.arrow c ec d ed)) :
    (Subtype leRow c a ∧ Subtype leRow b d) ∧ (leRow ec ea ∧ leRow eb ed) := by
  cases StructuralDecisions.Comparison.complete (leRow := leRow) rowTrans subtype with
  | refl => exact ⟨⟨.refl _, .refl _⟩, rowRefl _, rowRefl _⟩
  | arrow input inputRow output outputRow => exact ⟨⟨input.sound, output.sound⟩, inputRow, outputRow⟩
  | record shape => cases shape

private theorem variant_fields (leRow : RowType → RowType → Prop)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    {label label' : Nat} {a b : Ty RowType}
    (subtype : Subtype leRow (.variant label a) (.variant label' b)) :
    label = label' ∧ Subtype leRow a b := by
  cases StructuralDecisions.Comparison.complete (leRow := leRow) rowTrans subtype with
  | refl => exact ⟨rfl, .refl _⟩
  | variant payload => exact ⟨rfl, payload.sound⟩
  | record shape => cases shape

/-- Constructor decomposition and every mismatch check follow from the
independent structural subtype judgement. -/
theorem inspect_sound (leRow : RowType → RowType → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (value : Valuation n RowType) (source target : Node n RowType)
    {actualSource actualTarget : Ty RowType}
    (sourceShape : source.Holds value actualSource) (targetShape : target.Holds value actualTarget)
    (subtype : Subtype leRow actualSource actualTarget) :
    InspectionHolds leRow value (inspect source target) := by
  cases source <;> cases target
  all_goals try simp [inspect, InspectionHolds, Requirements.Holds]
  all_goals simp only [Node.Holds] at sourceShape targetShape
  all_goals subst actualSource; subst actualTarget
  case pair.pair a b c d =>
    simpa [inspect, InspectionHolds, Requirements.Holds, Edge.Holds] using pair_fields leRow rowTrans subtype
  case arrow.arrow a ea b eb c ec d ed =>
    simpa [inspect, InspectionHolds, Requirements.Holds, Edge.Holds] using arrow_fields leRow rowRefl rowTrans subtype
  case record.record source target =>
    obtain ⟨compatible, fields⟩ := record_inspect_sound leRow rowTrans value source target subtype
    simpa [inspect, compatible, InspectionHolds, Requirements.Holds] using fields
  case variant.variant label a label' b =>
    obtain ⟨same, payload⟩ := variant_fields leRow rowTrans subtype
    simpa [inspect, same, InspectionHolds, Requirements.Holds, Edge.Holds] using payload
  all_goals
    have heads := rigid_heads leRow rowTrans (by first | exact recordType_rigid value _ | rfl)
      (by first | exact recordType_rigid value _ | rfl) subtype
    try simp only [recordType_head] at heads
    simp only [head] at heads
    simp_all

/-! ## Finite constructor and variable rules -/

def allEdges (n : Nat) : List (Edge n) :=
  (List.finRange n).flatMap fun source => (List.finRange n).map fun target => (source, target)

@[simp] theorem mem_allEdges (edge : Edge n) : edge ∈ allEdges n := by
  obtain ⟨source, target⟩ := edge
  simp [allEdges]

theorem allEdges_length (n : Nat) : (allEdges n).length = n * n := by
  simp [allEdges, List.length_flatMap, List.map_const', List.sum_replicate_nat]

def seedRule (edge : Edge n) : FiniteHorn.Rule (Edge n) := ⟨[], edge⟩
def childRule (parent child : Edge n) : FiniteHorn.Rule (Edge n) := ⟨[parent], child⟩
def flowRule (pivot : Fin n) (edge : Edge n) : FiniteHorn.Rule (Edge n) :=
  ⟨[(edge.1, pivot), (pivot, edge.2)], edge⟩

def constructorRules (graph : Graph n RowType) (edge : Edge n) : List (FiniteHorn.Rule (Edge n)) :=
  match inspect (graph edge.1) (graph edge.2) with
  | none => []
  | some requirements => requirements.types.map (childRule edge)

def variableRules (graph : Graph n RowType) (pivot : Fin n) : List (FiniteHorn.Rule (Edge n)) :=
  match graph pivot with
  | .var => (allEdges n).map (flowRule pivot)
  | _ => []

def rules (graph : Graph n RowType) (constraints : List (Edge n)) : List (FiniteHorn.Rule (Edge n)) :=
  ((constraints.map seedRule) ++ (allEdges n).flatMap (constructorRules graph)) ++
    (List.finRange n).flatMap (variableRules graph)

def saturate (graph : Graph n RowType) (constraints : List (Edge n)) : List (Edge n) :=
  FiniteHorn.saturate (rules graph constraints) (allEdges n)

theorem saturate_nodup (graph : Graph n RowType) (constraints : List (Edge n)) :
    (saturate graph constraints).Nodup := FiniteHorn.saturate_nodup _ _

/-- The cache contains at most the square of the original node count.
Constructor nesting and cyclic bounds do not allocate new nodes. -/
theorem saturate_capacity (graph : Graph n RowType) (constraints : List (Edge n)) :
    (saturate graph constraints).length ≤ n * n := by
  rw [← allEdges_length]
  exact FiniteHorn.saturate_length_le _ _ mem_allEdges

theorem seedRule_mem (graph : Graph n RowType) (constraints : List (Edge n))
    {edge : Edge n} (member : edge ∈ constraints) : seedRule edge ∈ rules graph constraints := by
  unfold rules
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨edge, member, rfl⟩))

theorem childRule_mem (graph : Graph n RowType) (constraints : List (Edge n))
    (edge : Edge n) (requirements : Requirements n RowType)
    (found : inspect (graph edge.1) (graph edge.2) = some requirements)
    {child : Edge n} (member : child ∈ requirements.types) :
    childRule edge child ∈ rules graph constraints := by
  unfold rules
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨edge, mem_allEdges edge, ?_⟩
  simp only [constructorRules, found]
  exact List.mem_map.mpr ⟨child, member, rfl⟩

theorem flowRule_mem (graph : Graph n RowType) (constraints : List (Edge n))
    (pivot : Fin n) (isVariable : graph pivot = .var) (edge : Edge n) :
    flowRule pivot edge ∈ rules graph constraints := by
  unfold rules
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨pivot, by simp, ?_⟩
  simp only [variableRules, isVariable]
  exact List.mem_map.mpr ⟨edge, mem_allEdges edge, rfl⟩

theorem saturate_contains (graph : Graph n RowType) (constraints : List (Edge n))
    {edge : Edge n} (member : edge ∈ constraints) : edge ∈ saturate graph constraints := by
  apply FiniteHorn.saturate_closed _ _ mem_allEdges
  exact ⟨seedRule edge, seedRule_mem graph constraints member, rfl, by simp [seedRule]⟩

theorem saturate_constructor_closed (graph : Graph n RowType) (constraints : List (Edge n))
    {edge : Edge n} (present : edge ∈ saturate graph constraints)
    (requirements : Requirements n RowType)
    (found : inspect (graph edge.1) (graph edge.2) = some requirements)
    {child : Edge n} (member : child ∈ requirements.types) :
    child ∈ saturate graph constraints := by
  apply FiniteHorn.saturate_closed _ _ mem_allEdges
  exact ⟨childRule edge child, childRule_mem graph constraints edge requirements found member,
    rfl, by simpa [childRule, saturate] using present⟩

theorem saturate_variable_closed (graph : Graph n RowType) (constraints : List (Edge n))
    (pivot : Fin n) (isVariable : graph pivot = .var) (source target : Fin n)
    (lower : (source, pivot) ∈ saturate graph constraints)
    (upper : (pivot, target) ∈ saturate graph constraints) :
    (source, target) ∈ saturate graph constraints := by
  apply FiniteHorn.saturate_closed _ _ mem_allEdges
  refine ⟨flowRule pivot (source, target), flowRule_mem graph constraints pivot isVariable _, rfl, ?_⟩
  simpa [flowRule, saturate] using And.intro lower upper

def Closed (graph : Graph n RowType) (constraints cache : List (Edge n)) : Prop :=
  (∀ edge ∈ constraints, edge ∈ cache) ∧
  (∀ edge ∈ cache, ∀ requirements, inspect (graph edge.1) (graph edge.2) = some requirements →
    ∀ child ∈ requirements.types, child ∈ cache) ∧
  (∀ pivot, graph pivot = .var → ∀ source target,
    (source, pivot) ∈ cache → (pivot, target) ∈ cache → (source, target) ∈ cache)

theorem saturate_closed (graph : Graph n RowType) (constraints : List (Edge n)) :
    Closed graph constraints (saturate graph constraints) :=
  ⟨fun _ member => saturate_contains graph constraints member,
    fun _ present requirements found _ member =>
      saturate_constructor_closed graph constraints present requirements found member,
    saturate_variable_closed graph constraints⟩

theorem rules_valid (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (graph : Graph n RowType) (constraints : List (Edge n)) (value : Valuation n RowType)
    (model : Models leRow graph constraints value) :
    ∀ rule ∈ rules graph constraints, FiniteHorn.Valid (Edge.Holds leRow value) rule := by
  intro rule member premises
  rcases List.mem_append.mp member with initial | variables
  · rcases List.mem_append.mp initial with seeds | constructors
    · obtain ⟨edge, seedMember, rfl⟩ := List.mem_map.mp seeds
      exact model.2 edge seedMember
    · obtain ⟨edge, _, member⟩ := List.mem_flatMap.mp constructors
      cases found : inspect (graph edge.1) (graph edge.2) with
      | none => simp [constructorRules, found] at member
      | some requirements =>
          simp only [constructorRules, found] at member
          obtain ⟨child, childMember, rfl⟩ := List.mem_map.mp member
          have bound : edge.Holds leRow value := premises edge (by simp [childRule])
          have valid := inspect_sound leRow rowRefl rowTrans value (graph edge.1) (graph edge.2)
            (model.1 edge.1) (model.1 edge.2) bound
          rw [found] at valid
          exact valid.1 child childMember
  · obtain ⟨pivot, _, member⟩ := List.mem_flatMap.mp variables
    cases isVariable : graph pivot with
    | var =>
        simp only [variableRules, isVariable] at member
        obtain ⟨edge, _, rfl⟩ := List.mem_map.mp member
        exact .trans (premises (edge.1, pivot) (by simp [flowRule]))
          (premises (pivot, edge.2) (by simp [flowRule]))
    | _ => simp [variableRules, isVariable] at member

/-- Every inserted obligation is already true in every original model. -/
theorem saturate_preserves (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (graph : Graph n RowType) (constraints : List (Edge n)) (value : Valuation n RowType)
    (model : Models leRow graph constraints value) : Models leRow graph (saturate graph constraints) value :=
  ⟨model.1, FiniteHorn.saturate_preserves _ _ _ (rules_valid leRow rowRefl rowTrans graph constraints value model)⟩

/-- Saturation preserves the complete model set, not just one chosen assignment. -/
theorem saturate_models_iff (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (graph : Graph n RowType) (constraints : List (Edge n)) (value : Valuation n RowType) :
    Models leRow graph (saturate graph constraints) value ↔ Models leRow graph constraints value := by
  constructor
  · intro model
    exact ⟨model.1, fun edge member => model.2 edge (saturate_contains graph constraints member)⟩
  · exact saturate_preserves leRow rowRefl rowTrans graph constraints value

def inspectionAccepted (rowCheck : RowType → RowType → Bool) : Option (Requirements n RowType) → Bool
  | none => false
  | some requirements => requirements.rows.all fun row => rowCheck row.1 row.2

def consistent (rowCheck : RowType → RowType → Bool) (graph : Graph n RowType)
    (cache : List (Edge n)) : Bool :=
  cache.all fun edge => inspectionAccepted rowCheck (inspect (graph edge.1) (graph edge.2))

theorem consistent_inspect (rowCheck : RowType → RowType → Bool) (graph : Graph n RowType)
    (cache : List (Edge n)) (accepted : consistent rowCheck graph cache = true)
    {edge : Edge n} (member : edge ∈ cache) :
    ∃ requirements, inspect (graph edge.1) (graph edge.2) = some requirements ∧
      ∀ row ∈ requirements.rows, rowCheck row.1 row.2 = true := by
  have checked := List.all_eq_true.mp accepted edge member
  cases found : inspect (graph edge.1) (graph edge.2) with
  | none => simp [found, inspectionAccepted] at checked
  | some requirements =>
      rw [found] at checked
      exact ⟨requirements, rfl, List.all_eq_true.mp checked⟩

/-- `some` reports a saturated, mismatch-free cache. It does not assert a
finite or recursive solution assignment without its construction theorem. -/
def solve (rowCheck : RowType → RowType → Bool) (graph : Graph n RowType)
    (constraints : List (Edge n)) : Option (List (Edge n)) :=
  let cache := saturate graph constraints
  if consistent rowCheck graph cache then some cache else none

theorem consistent_of_models (rowCheck : RowType → RowType → Bool)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : Graph n RowType) (cache : List (Edge n)) (value : Valuation n RowType)
    (model : Models leRow graph cache value) : consistent rowCheck graph cache = true := by
  apply List.all_eq_true.mpr
  intro edge member
  have valid := inspect_sound leRow rowRefl rowTrans value (graph edge.1) (graph edge.2)
    (model.1 edge.1) (model.1 edge.2) (model.2 edge member)
  cases found : inspect (graph edge.1) (graph edge.2) with
  | none => simp [found, InspectionHolds] at valid
  | some requirements =>
      rw [found] at valid
      apply List.all_eq_true.mpr
      intro row member
      exact (rowExact row.1 row.2).mpr (valid.2 row member)

theorem solve_some_iff (rowCheck : RowType → RowType → Bool) (graph : Graph n RowType)
    (constraints cache : List (Edge n)) :
    solve rowCheck graph constraints = some cache ↔
      cache = saturate graph constraints ∧ consistent rowCheck graph cache = true := by
  simp only [solve]
  split
  · rename_i accepted
    constructor
    · intro same
      have equal := Option.some.inj same
      exact ⟨equal.symm, equal ▸ accepted⟩
    · rintro ⟨rfl, _⟩
      rfl
  · rename_i rejected
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨rfl, accepted⟩
      exact False.elim (rejected accepted)

theorem solve_closed (rowCheck : RowType → RowType → Bool) (graph : Graph n RowType)
    (constraints cache : List (Edge n)) (solved : solve rowCheck graph constraints = some cache) :
    Closed graph constraints cache ∧ consistent rowCheck graph cache = true := by
  obtain ⟨rfl, consistent⟩ := (solve_some_iff rowCheck graph constraints cache).mp solved
  exact ⟨saturate_closed graph constraints, consistent⟩

/-- A mismatch rejects every assignment of arbitrary structural types to
the unknowns. No supplied model or satisfiability assumption is required. -/
theorem solve_rejects (rowCheck : RowType → RowType → Bool)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : Graph n RowType) (constraints : List (Edge n))
    (rejected : solve rowCheck graph constraints = none) :
    ¬ ∃ value, Models leRow graph constraints value := by
  rintro ⟨value, model⟩
  have accepted := consistent_of_models rowCheck leRow rowRefl rowTrans rowExact graph _ value
    (saturate_preserves leRow rowRefl rowTrans graph constraints value model)
  simp only [solve, accepted, ↓reduceIte] at rejected
  cases rejected

end Yulang.NestedValueSolver
