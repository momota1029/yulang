import Yulang.CasePatterns
import Yulang.VariantsMerged

/-!
# Conservative executable exhaustiveness for resolved patterns

This finite structural coverage kernel splits booleans, unit, products,
list nil/cons and unions. Variant payloads are deliberately not split into
separate outer cells: this conservative checker requires one unguarded arm
covering the whole merged payload before its tag can be subtracted. It never
invents partial payload residuals. The single-arm sufficient condition is
not a new restriction on source programs.

The checker is exact for the independent inductive judgement below, and
accepted coverage is sound for every value in the domain, not a finite
sample. This is not the full Rust pattern-matrix algorithm: arbitrary
integer interval unions and arbitrary semantic type predicates are outside
this fragment. Default types and successful typed default evaluation are
explicit parameters; no default-expression scope/effect policy is chosen.
-/

namespace Yulang.CaseCoverage

open CaseValues CasePatterns LiteralValues EvaluationTrace

/-- Finite descriptions of semantic input domains. `required` and `optional`
intersect a field fact with the remaining record constraints. -/
inductive Domain where
  | any
  | base : Kind → Domain
  | boolValue : Bool → Domain
  | unitValue
  | intValue : Int → Domain
  | strValue : String → Domain
  | pair : Domain → Domain → Domain
  | records
  | required : Nat → Domain → Domain → Domain
  | optional : Nat → Domain → Domain → Domain
  | nil
  | cons : Domain → Domain → Domain
  | list : Domain → Domain
  | variant : Nat → Domain → Domain
  | nominal : Nat → Nat → Domain → Domain
  | union : Domain → Domain → Domain
  deriving DecidableEq, Repr

def Domain.denote (F : Type) : Domain → Ty F
  | .any => Ty.any
  | .base kind => Ty.literal kind
  | .boolValue value => Ty.exact (.literal (.bool value))
  | .unitValue => Ty.exact (.literal .unit)
  | .intValue value => Ty.exact (.literal (.int value))
  | .strValue value => Ty.exact (.literal (.str value))
  | .pair first last => Ty.pair (first.denote F) (last.denote F)
  | .records => Ty.records
  | .required name payload rest => Ty.inter (Ty.required name (payload.denote F)) (rest.denote F)
  | .optional name payload rest => Ty.inter (Ty.optional name (payload.denote F)) (rest.denote F)
  | .nil => Ty.exact (.list [])
  | .cons head tail => fun value => match value with
      | .list (first :: rest) => head.denote F first ∧ tail.denote F (.list rest)
      | _ => False
  | .list element => Ty.list (element.denote F)
  | .variant tag payload => Ty.variant tag (payload.denote F)
  | .nominal typeId ctorId payload => Ty.nominal typeId ctorId (payload.denote F)
  | .union left right => Ty.union (left.denote F) (right.denote F)

/-- A finite, executable partition. Variant and nominal payloads remain whole. -/
def cells : Domain → List Domain
  | .base .bool => [.boolValue false, .boolValue true]
  | .base .unit => [.unitValue]
  | .pair first last => (cells first).flatMap fun a => (cells last).map (.pair a)
  | .cons head tail => (cells head).flatMap fun a => (cells tail).map (.cons a)
  | .list element => .nil :: (cells element).map (fun head => .cons head (.list element))
  | .union left right => cells left ++ cells right
  | other => [other]

/-- Independent structural partition judgement, without a call to `cells`. -/
inductive Cell : Domain → Domain → Prop where
  | any : Cell .any .any
  | int : Cell (.base .int) (.base .int)
  | float : Cell (.base .float) (.base .float)
  | str : Cell (.base .str) (.base .str)
  | bool (value : Bool) : Cell (.base .bool) (.boolValue value)
  | unit : Cell (.base .unit) .unitValue
  | boolValue : Cell (.boolValue value) (.boolValue value)
  | unitValue : Cell .unitValue .unitValue
  | intValue : Cell (.intValue value) (.intValue value)
  | strValue : Cell (.strValue value) (.strValue value)
  | pair : Cell first a → Cell last b → Cell (.pair first last) (.pair a b)
  | records : Cell .records .records
  | required : Cell (.required name payload rest) (.required name payload rest)
  | optional : Cell (.optional name payload rest) (.optional name payload rest)
  | nil : Cell .nil .nil
  | cons : Cell head a → Cell tail b → Cell (.cons head tail) (.cons a b)
  | listNil : Cell (.list element) .nil
  | listCons : Cell element head → Cell (.list element) (.cons head (.list element))
  | variant : Cell (.variant tag payload) (.variant tag payload)
  | nominal : Cell (.nominal typeId ctorId payload) (.nominal typeId ctorId payload)
  | unionLeft : Cell left cell → Cell (.union left right) cell
  | unionRight : Cell right cell → Cell (.union left right) cell

theorem Cell.mem (partition : Cell input cell) : cell ∈ cells input := by
  induction partition with
  | bool value => cases value <;> simp [cells]
  | pair _ _ first last | cons _ _ first last =>
      simp only [cells, List.mem_flatMap, List.mem_map]
      exact ⟨_, first, _, last, rfl⟩
  | listCons _ ih => simp [cells, ih]
  | unionLeft _ ih => simp [cells, ih]
  | unionRight _ ih => simp [cells, ih]
  | _ => simp [cells]

theorem cell_of_mem (input : Domain) (cell : Domain) (member : cell ∈ cells input) :
    Cell input cell := by
  induction input generalizing cell with
  | base kind =>
      cases kind with
      | int | float | str => simp only [cells, List.mem_singleton] at member; subst cell; constructor
      | bool =>
          simp only [cells, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with same | same <;> subst cell <;> exact .bool _
      | unit => simp only [cells, List.mem_singleton] at member; subst cell; exact .unit
  | pair first last ihf ihl | cons first last ihf ihl =>
      simp only [cells, List.mem_flatMap, List.mem_map] at member
      rcases member with ⟨a, ha, b, hb, same⟩
      subst cell
      constructor
      · exact ihf a ha
      · exact ihl b hb
  | list element ih =>
      simp only [cells, List.mem_cons, List.mem_map] at member
      rcases member with same | ⟨head, member, same⟩
      · subst cell; exact .listNil
      · subst cell; exact .listCons (ih head member)
  | union left right ihl ihr =>
      simp only [cells, List.mem_append] at member
      rcases member with member | member
      · exact .unionLeft (ihl cell member)
      · exact .unionRight (ihr cell member)
  | _ => simp only [cells, List.mem_singleton] at member; subst cell; constructor

theorem cells_exact (input cell : Domain) : cell ∈ cells input ↔ Cell input cell :=
  ⟨cell_of_mem input cell, Cell.mem⟩

/-- Every semantic value belongs to an actual generated cell. No enumeration
of values or finiteness assumption on payloads is used. -/
theorem domain_has_cell (input : Domain) (value : Value F) (valid : input.denote F value) :
    ∃ cell, Cell input cell ∧ cell.denote F value := by
  induction input generalizing value with
  | base kind =>
      cases kind with
      | int | float | str => exact ⟨_, by constructor, valid⟩
      | bool =>
          cases value with
          | literal actual =>
              cases actual <;> simp_all [Domain.denote, Ty.literal, Literal.kind]
              exact ⟨_, .bool _, rfl⟩
          | _ => cases valid
      | unit =>
          cases value with
          | literal actual =>
              cases actual <;> simp_all [Domain.denote, Ty.literal, Literal.kind]
              exact ⟨_, .unit, rfl⟩
          | _ => cases valid
  | pair first last ihf ihl =>
      cases value with
      | pair a b =>
          obtain ⟨x, hx, ax⟩ := ihf a valid.1
          obtain ⟨y, hy, vy⟩ := ihl b valid.2
          exact ⟨_, .pair hx hy, ax, vy⟩
      | _ => cases valid
  | cons head tail ihh iht =>
      cases value with
      | list values =>
          cases values with
          | nil => cases valid
          | cons first rest =>
              obtain ⟨a, ha, va⟩ := ihh first valid.1
              obtain ⟨b, hb, vb⟩ := iht (.list rest) valid.2
              exact ⟨_, .cons ha hb, va, vb⟩
      | _ => cases valid
  | list element ih =>
      cases value with
      | list values =>
          cases values with
          | nil => exact ⟨_, .listNil, rfl⟩
          | cons first rest =>
              obtain ⟨head, partition, typed⟩ := ih first (valid first (by simp))
              exact ⟨_, .listCons partition, typed, fun v member => valid v (by simp [member])⟩
      | _ => cases valid
  | union left right ihl ihr =>
      rcases valid with valid | valid
      · obtain ⟨cell, partition, typed⟩ := ihl value valid
        exact ⟨cell, .unionLeft partition, typed⟩
      · obtain ⟨cell, partition, typed⟩ := ihr value valid
        exact ⟨cell, .unionRight partition, typed⟩
  | _ => exact ⟨_, by constructor, valid⟩

inductive RecordDomain : Domain → Prop where
  | records : RecordDomain .records
  | required : RecordDomain (.required name payload rest)
  | optional : RecordDomain (.optional name payload rest)

def recordCheck : Domain → Bool
  | .records | .required .. | .optional .. => true
  | _ => false

theorem recordCheck_exact (input : Domain) : recordCheck input = true ↔ RecordDomain input := by
  constructor
  · intro h
    cases input <;> simp only [recordCheck, Bool.false_eq_true] at h <;> constructor
  · intro h
    cases h <;> rfl

inductive RequiredField : Domain → Nat → Domain → Prop where
  | here : RequiredField (.required name payload rest) name payload
  | required : name ≠ key → RequiredField rest name payload →
      RequiredField (.required key other rest) name payload
  | optional : RequiredField rest name payload →
      RequiredField (.optional key other rest) name payload

inductive OptionalField : Domain → Nat → Domain → Prop where
  | here : OptionalField (.optional name payload rest) name payload
  | optional : name ≠ key → OptionalField rest name payload →
      OptionalField (.optional key other rest) name payload
  | required : OptionalField rest name payload →
      OptionalField (.required key other rest) name payload

def requiredAt (name : Nat) : Domain → Option Domain
  | .required key payload rest => if name = key then some payload else requiredAt name rest
  | .optional _ _ rest => requiredAt name rest
  | _ => none

def optionalAt (name : Nat) : Domain → Option Domain
  | .optional key payload rest => if name = key then some payload else optionalAt name rest
  | .required _ _ rest => optionalAt name rest
  | _ => none


theorem RequiredField.lookup (field : RequiredField input name payload) :
    requiredAt name input = some payload := by
  induction field with
  | here => simp [requiredAt]
  | required different _ ih => simp [requiredAt, different, ih]
  | optional _ ih => exact ih

theorem OptionalField.lookup (field : OptionalField input name payload) :
    optionalAt name input = some payload := by
  induction field with
  | here => simp [optionalAt]
  | optional different _ ih => simp [optionalAt, different, ih]
  | required _ ih => exact ih

theorem requiredAt_exact (input : Domain) (name : Nat) (payload : Domain) :
    requiredAt name input = some payload ↔ RequiredField input name payload := by
  constructor
  · intro found
    induction input with
    | required key other rest _ ih =>
        by_cases same : name = key
        · subst key
          simp only [requiredAt, ↓reduceIte, Option.some.injEq] at found
          subst payload
          exact .here
        · exact .required same (ih (by simpa [requiredAt, same] using found))
    | optional _ _ _ _ ih => exact .optional (ih found)
    | _ => cases found
  · exact RequiredField.lookup

theorem optionalAt_exact (input : Domain) (name : Nat) (payload : Domain) :
    optionalAt name input = some payload ↔ OptionalField input name payload := by
  constructor
  · intro found
    induction input with
    | optional key other rest _ ih =>
        by_cases same : name = key
        · subst key
          simp only [optionalAt, ↓reduceIte, Option.some.injEq] at found
          subst payload
          exact .here
        · exact .optional same (ih (by simpa [optionalAt, same] using found))
    | required _ _ _ _ ih => exact .required (ih found)
    | _ => cases found
  · exact OptionalField.lookup

theorem RecordDomain.values (record : RecordDomain input) (value : Value F)
    (valid : input.denote F value) : ∃ fields, value = .record fields := by
  cases record with
  | records => cases value <;> first | exact ⟨_, rfl⟩ | cases valid
  | required => cases value <;> first | exact ⟨_, rfl⟩ | cases valid.1
  | optional => cases value <;> first | exact ⟨_, rfl⟩ | cases valid.1

theorem RequiredField.values (field : RequiredField input name payload) (value : Value F)
    (valid : input.denote F value) : Ty.required name (payload.denote F) value := by
  induction field with
  | here => exact valid.1
  | required _ _ ih | optional _ ih => exact ih valid.2

theorem OptionalField.values (field : OptionalField input name payload) (value : Value F)
    (valid : input.denote F value) : Ty.optional name (payload.denote F) value := by
  induction field with
  | here => exact valid.1
  | optional _ _ ih | required _ ih => exact ih valid.2

inductive LiteralCell : Literal F → Domain → Prop where
  | bool (value : Bool) : LiteralCell (.bool value) (.boolValue value)
  | unit : LiteralCell .unit .unitValue
  | int (value : Int) : LiteralCell (.int value) (.intValue value)
  | str (value : String) : LiteralCell (.str value) (.strValue value)

def literalCellCheck : Literal F → Domain → Bool
  | .bool a, .boolValue b => decide (a = b)
  | .unit, .unitValue => true
  | .int a, .intValue b => decide (a = b)
  | .str a, .strValue b => decide (a = b)
  | _, _ => false

theorem literalCellCheck_exact (literal : Literal F) (cell : Domain) :
    literalCellCheck literal cell = true ↔ LiteralCell literal cell := by
  constructor
  · intro checked
    cases literal <;> cases cell <;>
      simp only [literalCellCheck, Bool.false_eq_true, decide_eq_true_eq] at checked
    all_goals subst_vars; constructor
  · intro matched
    cases matched <;> simp [literalCellCheck]

inductive RangeCell (lower upper : Option Int) : Domain → Prop where
  | int : lower.isSome ∨ upper.isSome → InIntRange lower upper value →
      RangeCell lower upper (.intValue value)

def rangeCellCheck (lower upper : Option Int) : Domain → Bool
  | .intValue value => (lower.isSome || upper.isSome) &&
      intRangeCheck lower upper (.int value : Literal Empty)
  | _ => false

theorem rangeCellCheck_exact (lower upper : Option Int) (cell : Domain) :
    rangeCellCheck lower upper cell = true ↔ RangeCell lower upper cell := by
  constructor
  · intro checked
    cases cell <;> simp only [rangeCellCheck, Bool.false_eq_true] at checked
    rcases Bool.and_eq_true_iff.mp checked with ⟨nonempty, range⟩
    have bounds := (intRangeCheck_exact _ _ _).mp range
    cases bounds with
    | int valid => exact .int (by simpa using nonempty) valid
  · intro matched
    cases matched with
    | int nonempty valid =>
        simp only [rangeCellCheck, Bool.and_eq_true]
        exact ⟨by simpa using nonempty, (intRangeCheck_exact _ _ _).mpr (.int valid)⟩

mutual
  /-- One pattern is total on every structural cell of its input domain. -/
  inductive Total (defaults : D → Domain) : Pattern F D → Domain → Prop where
    | cells : (∀ cell, Cell input cell → Handles defaults pattern cell) →
        Total defaults pattern input

  /-- Independent structural rules for a single cell. The judgement has no
  checker call, evaluator-success premise, or enumerated sample of values. -/
  inductive Handles (defaults : D → Domain) : Pattern F D → Domain → Prop where
    | wildcard : Handles defaults .wildcard input
    | bind : Handles defaults (.bind name) input
    | literal : LiteralCell literal cell → Handles defaults (.literal literal) cell
    | intRange : RangeCell lower upper cell → Handles defaults (.intRange lower upper) cell
    | pair : Total defaults p first → Total defaults q last →
        Handles defaults (.pair p q) (.pair first last)
    | recordEnd : RecordDomain input → Handles defaults .recordEnd input
    | field : RequiredField input name payload → Total defaults p payload → Total defaults rest input →
        Handles defaults (.field name p rest) input
    | defaultField : OptionalField input name payload →
        Total defaults p (.union payload (defaults fallback)) → Total defaults rest input →
        Handles defaults (.defaultField name fallback p rest) input
    | nil : Handles defaults .nil .nil
    | cons : Total defaults p first → Total defaults rest tail →
        Handles defaults (.cons p rest) (.cons first tail)
    | snoc : Total defaults init (.list .any) → Total defaults last .any →
        Handles defaults (.snoc init last) (.cons head tail)
    | variant : Total defaults p payload → Handles defaults (.variant tag p) (.variant tag payload)
    | nominal : Total defaults p payload →
        Handles defaults (.nominal typeId ctorId p) (.nominal typeId ctorId payload)
    | orLeft : Total defaults p input → Handles defaults (.or p q) input
    | orRight : Total defaults q input → Handles defaults (.or p q) input
    | as : Total defaults p input → Handles defaults (.as p name) input
end

theorem total_iff (defaults : D → Domain) (pattern : Pattern F D) (input : Domain) :
    Total defaults pattern input ↔ ∀ cell, Cell input cell → Handles defaults pattern cell := by
  constructor
  · intro total
    cases total with
    | cells parts => exact parts
  · exact .cells

/-- Executable structural totality. Literal floats are deliberately not
recognized as exhaustive; their comparison policy is not fixed here. -/
def checkOne (defaults : D → Domain) : Pattern F D → Domain → Bool
  | .wildcard, _ => true
  | .bind _, _ => true
  | .literal literal, input => (cells input).all (literalCellCheck literal)
  | .intRange lower upper, input => (cells input).all (rangeCellCheck lower upper)
  | .pair p q, input => (cells input).all fun cell => match cell with
      | .pair first last => checkOne defaults p first && checkOne defaults q last
      | _ => false
  | .recordEnd, input => (cells input).all recordCheck
  | .field name p rest, input => (cells input).all fun cell =>
      match requiredAt name cell with
      | none => false
      | some payload => checkOne defaults p payload && checkOne defaults rest cell
  | .defaultField name fallback p rest, input => (cells input).all fun cell =>
      match optionalAt name cell with
      | none => false
      | some payload => checkOne defaults p (.union payload (defaults fallback)) && checkOne defaults rest cell
  | .nil, input => (cells input).all fun cell => decide (cell = .nil)
  | .cons p rest, input => (cells input).all fun cell => match cell with
      | .cons first tail => checkOne defaults p first && checkOne defaults rest tail
      | _ => false
  | .snoc init last, input => (cells input).all fun cell => match cell with
      | .cons _ _ => checkOne defaults init (.list .any) && checkOne defaults last .any
      | _ => false
  | .variant tag p, input => (cells input).all fun cell => match cell with
      | .variant actual payload => decide (tag = actual) && checkOne defaults p payload
      | _ => false
  | .nominal typeId ctorId p, input => (cells input).all fun cell => match cell with
      | .nominal actualType actualCtor payload =>
          decide (typeId = actualType ∧ ctorId = actualCtor) && checkOne defaults p payload
      | _ => false
  | .or p q, input => (cells input).all fun cell => checkOne defaults p cell || checkOne defaults q cell
  | .as p _, input => (cells input).all fun cell => checkOne defaults p cell


@[simp] theorem handles_wildcard (defaults : D → Domain) (input : Domain) :
    Handles (F := F) defaults .wildcard input := .wildcard

@[simp] theorem handles_bind (defaults : D → Domain) (input : Domain) (name : Nat) :
    Handles (F := F) defaults (.bind name) input := .bind

theorem handles_literal_iff (defaults : D → Domain) (literal : Literal F) (input : Domain) :
    Handles defaults (.literal literal) input ↔ LiteralCell literal input := by
  constructor
  · intro total; cases total with | literal matched => exact matched
  · exact .literal

theorem handles_range_iff (defaults : D → Domain) (lower upper : Option Int) (input : Domain) :
    Handles (F := F) defaults (.intRange lower upper) input ↔ RangeCell lower upper input := by
  constructor
  · intro total; cases total with | intRange matched => exact matched
  · exact .intRange

theorem handles_pair_iff (defaults : D → Domain) (p q : Pattern F D) (input : Domain) :
    Handles defaults (.pair p q) input ↔ match input with
      | .pair first last => Total defaults p first ∧ Total defaults q last
      | _ => False := by
  constructor
  · intro total; cases total with | pair first last => exact ⟨first, last⟩
  · cases input <;> intro valid <;> try contradiction
    exact .pair valid.1 valid.2

theorem handles_recordEnd_iff (defaults : D → Domain) (input : Domain) :
    Handles (F := F) defaults .recordEnd input ↔ RecordDomain input := by
  constructor
  · intro total; cases total with | recordEnd record => exact record
  · exact .recordEnd

theorem handles_field_iff (defaults : D → Domain) (name : Nat) (p rest : Pattern F D) (input : Domain) :
    Handles defaults (.field name p rest) input ↔
      ∃ payload, RequiredField input name payload ∧ Total defaults p payload ∧ Total defaults rest input := by
  constructor
  · intro total; cases total with | field selected head tail => exact ⟨_, selected, head, tail⟩
  · rintro ⟨_, selected, head, tail⟩; exact .field selected head tail

theorem handles_default_iff (defaults : D → Domain) (name : Nat) (fallback : D)
    (p rest : Pattern F D) (input : Domain) :
    Handles defaults (.defaultField name fallback p rest) input ↔
      ∃ payload, OptionalField input name payload ∧
        Total defaults p (.union payload (defaults fallback)) ∧ Total defaults rest input := by
  constructor
  · intro total; cases total with | defaultField selected head tail => exact ⟨_, selected, head, tail⟩
  · rintro ⟨_, selected, head, tail⟩; exact .defaultField selected head tail

theorem handles_nil_iff (defaults : D → Domain) (input : Domain) :
    Handles (F := F) defaults .nil input ↔ input = .nil := by
  constructor
  · intro total; cases total; rfl
  · intro same; subst input; exact .nil

theorem handles_cons_iff (defaults : D → Domain) (p q : Pattern F D) (input : Domain) :
    Handles defaults (.cons p q) input ↔ match input with
      | .cons first tail => Total defaults p first ∧ Total defaults q tail
      | _ => False := by
  constructor
  · intro total; cases total with | cons first tail => exact ⟨first, tail⟩
  · cases input <;> intro valid <;> try contradiction
    exact .cons valid.1 valid.2

theorem handles_snoc_iff (defaults : D → Domain) (p q : Pattern F D) (input : Domain) :
    Handles defaults (.snoc p q) input ↔ match input with
      | .cons _ _ => Total defaults p (.list .any) ∧ Total defaults q .any
      | _ => False := by
  constructor
  · intro total; cases total with | snoc init last => exact ⟨init, last⟩
  · cases input <;> intro valid <;> try contradiction
    exact .snoc valid.1 valid.2

theorem handles_variant_iff (defaults : D → Domain) (tag : Nat) (p : Pattern F D) (input : Domain) :
    Handles defaults (.variant tag p) input ↔ match input with
      | .variant actual payload => tag = actual ∧ Total defaults p payload
      | _ => False := by
  constructor
  · intro total; cases total with | variant payload => exact ⟨rfl, payload⟩
  · cases input <;> intro valid <;> try contradiction
    rcases valid with ⟨same, payload⟩
    subst tag
    exact .variant payload

theorem handles_nominal_iff (defaults : D → Domain) (typeId ctorId : Nat)
    (p : Pattern F D) (input : Domain) :
    Handles defaults (.nominal typeId ctorId p) input ↔ match input with
      | .nominal actualType actualCtor payload =>
          (typeId = actualType ∧ ctorId = actualCtor) ∧ Total defaults p payload
      | _ => False := by
  constructor
  · intro total; cases total with | nominal payload => exact ⟨⟨rfl, rfl⟩, payload⟩
  · cases input <;> intro valid <;> try contradiction
    rcases valid with ⟨⟨sameType, sameCtor⟩, payload⟩
    subst typeId; subst ctorId
    exact .nominal payload

theorem handles_or_iff (defaults : D → Domain) (p q : Pattern F D) (input : Domain) :
    Handles defaults (.or p q) input ↔ Total defaults p input ∨ Total defaults q input := by
  constructor
  · intro total
    cases total with
    | orLeft first => exact .inl first
    | orRight last => exact .inr last
  · intro total
    exact total.elim Handles.orLeft Handles.orRight

theorem handles_as_iff (defaults : D → Domain) (p : Pattern F D) (name : Nat) (input : Domain) :
    Handles defaults (.as p name) input ↔ Total defaults p input := by
  constructor
  · intro total; cases total with | as inner => exact inner
  · exact .as

/-- Exactness is against independent structural rules, not against a
proposition defined as the checker returning true. -/
theorem checkOne_exact (defaults : D → Domain) (pattern : Pattern F D) (input : Domain) :
    checkOne defaults pattern input = true ↔ Total defaults pattern input := by
  induction pattern generalizing input with
  | wildcard => simp [checkOne, total_iff]
  | bind name => simp [checkOne, total_iff]
  | literal literal =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, literalCellCheck_exact, handles_literal_iff]
  | intRange lower upper =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, rangeCellCheck_exact, handles_range_iff]
  | recordEnd =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, recordCheck_exact, handles_recordEnd_iff]
  | nil =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, decide_eq_true_eq, handles_nil_iff]
  | pair p q ihp ihq =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_pair_iff]
      apply forall_congr'; intro cell
      apply imp_congr_right; intro _
      cases cell <;> simp only [Bool.false_eq_true, Bool.and_eq_true, ihp, ihq]
  | cons p q ihp ihq =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_cons_iff]
      apply forall_congr'; intro cell
      apply imp_congr_right; intro _
      cases cell <;> simp only [Bool.false_eq_true, Bool.and_eq_true, ihp, ihq]
  | snoc p q ihp ihq =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_snoc_iff]
      apply forall_congr'; intro cell
      apply imp_congr_right; intro _
      cases cell <;> simp only [Bool.false_eq_true, Bool.and_eq_true, ihp, ihq]
  | variant tag p ih =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_variant_iff]
      apply forall_congr'; intro cell
      apply imp_congr_right; intro _
      cases cell <;> simp only [Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
  | nominal typeId ctorId p ih =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_nominal_iff]
      apply forall_congr'; intro cell
      apply imp_congr_right; intro _
      cases cell <;> simp only [Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq, ih]
  | field name p rest ihp ihr =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_field_iff, ← requiredAt_exact]
      apply forall_congr'; intro cell
      apply imp_congr_right; intro _
      cases found : requiredAt name cell <;> simp [ihp, ihr]
  | defaultField name fallback p rest ihp ihr =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_default_iff, ← optionalAt_exact]
      apply forall_congr'; intro cell
      apply imp_congr_right; intro _
      cases found : optionalAt name cell <;> simp [ihp, ihr]
  | or p q ihp ihq =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, Bool.or_eq_true, handles_or_iff, ihp, ihq]
  | as p name ih =>
      rw [total_iff]
      simp only [checkOne, List.all_eq_true, cells_exact, handles_as_iff, ih]


/-- All syntactically occurring default leaves, including both sides of `or`.
The list localizes the leaf soundness premise; unused codes need not evaluate. -/
def patternDefaults : Pattern F D → List D
  | .wildcard | .bind _ | .literal _ | .intRange _ _ | .recordEnd | .nil => []
  | .pair p q | .field _ p q | .cons p q | .snoc p q | .or p q => patternDefaults p ++ patternDefaults q
  | .defaultField _ code p rest => code :: (patternDefaults p ++ patternDefaults rest)
  | .variant _ p | .nominal _ _ p | .as p _ => patternDefaults p

/-- Only the existence of a guard is relevant to static coverage. Its
expression, result and effects are deliberately absent from this record. -/
structure Arm (F D : Type) where
  pattern : Pattern F D
  guarded : Bool
  deriving Repr

def armDefaults (arms : List (Arm F D)) : List D :=
  arms.flatMap fun arm => patternDefaults arm.pattern

/-- Different cells may be covered by different unguarded arms. -/
inductive Covered (defaults : D → Domain) (arms : List (Arm F D)) (input : Domain) : Prop where
  | cells : (∀ cell, Cell input cell →
      ∃ arm ∈ arms, arm.guarded = false ∧ Total defaults arm.pattern cell) →
      Covered defaults arms input

def check (defaults : D → Domain) (arms : List (Arm F D)) (input : Domain) : Bool :=
  (cells input).all fun cell => arms.any fun arm => !arm.guarded && checkOne defaults arm.pattern cell

theorem covered_iff (defaults : D → Domain) (arms : List (Arm F D)) (input : Domain) :
    Covered defaults arms input ↔ ∀ cell, Cell input cell →
      ∃ arm ∈ arms, arm.guarded = false ∧ Total defaults arm.pattern cell := by
  constructor
  · intro coverage; cases coverage with | cells parts => exact parts
  · exact .cells

/-- Guarded arms never contribute, regardless of whether the guard is
extensionally true. The specification's guard exclusion is structural. -/
theorem check_exact (defaults : D → Domain) (arms : List (Arm F D)) (input : Domain) :
    check defaults arms input = true ↔ Covered defaults arms input := by
  rw [covered_iff]
  simp only [check, List.all_eq_true, List.any_eq_true, cells_exact,
    Bool.and_eq_true, Bool.not_eq, Bool.not_eq_true, checkOne_exact]

theorem guarded_cons_ignored (defaults : D → Domain) (arm : Arm F D) (arms : List (Arm F D))
    (input : Domain) (guarded : arm.guarded = true) :
    check defaults (arm :: arms) input = check defaults arms input := by
  simp [check, guarded]

abbrev VariantRow := Variants.Merged.Row Nat Domain

/-- The row is already merged: one entry per tag and the complete payload. -/
inductive VariantsCovered (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) : Prop where
  | tags : (∀ tag payload, (tag, payload) ∈ row.entries →
      Covered defaults arms (.variant tag payload)) → VariantsCovered defaults arms row

def checkVariants (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) : Bool :=
  row.entries.all fun entry => check defaults arms (.variant entry.1 entry.2)

theorem variantsCovered_iff (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) :
    VariantsCovered defaults arms row ↔ ∀ tag payload, (tag, payload) ∈ row.entries →
      Covered defaults arms (.variant tag payload) := by
  constructor
  · intro coverage; cases coverage with | tags entries => exact entries
  · exact .tags

theorem checkVariants_exact (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) :
    checkVariants defaults arms row = true ↔ VariantsCovered defaults arms row := by
  rw [variantsCovered_iff]
  simp only [checkVariants, List.all_eq_true, check_exact]
  constructor
  · intro covered tag payload member; exact covered (tag, payload) member
  · intro covered ⟨tag, payload⟩ member; exact covered tag payload member

def handledTag (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) (tag : Nat) : Bool :=
  match Variants.Merged.lookup tag row with
  | none => false
  | some payload => check defaults arms (.variant tag payload)

def residual (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) : VariantRow :=
  Variants.Merged.residual (handledTag defaults arms row) row

/-- An accepted whole payload removes its tag; a rejected whole payload is
retained literally. No proposed partial payload enters the residual row. -/
theorem residual_lookup (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) (tag : Nat) :
    Variants.Merged.lookup tag (residual defaults arms row) =
      match Variants.Merged.lookup tag row with
      | none => none
      | some payload => if check defaults arms (.variant tag payload) then none else some payload := by
  rw [residual, Variants.Merged.lookup_residual]
  cases found : Variants.Merged.lookup tag row <;> simp [handledTag, found]

/-- This is the connection to decision 4's existing merged-row theorem. -/
theorem residual_empty_iff (defaults : D → Domain) (arms : List (Arm F D)) (row : VariantRow) :
    (residual defaults arms row).entries = [] ↔ VariantsCovered defaults arms row := by
  rw [residual, Variants.Merged.residual_empty_iff, variantsCovered_iff]
  constructor
  · intro empty tag payload member
    have found := (Variants.Merged.mem_iff_lookup tag payload row).mp member
    have checked := empty tag payload found
    exact (check_exact _ _ _).mp (by simpa [handledTag, found] using checked)
  · intro covered tag payload found
    have valid := covered tag payload ((Variants.Merged.mem_iff_lookup tag payload row).mpr found)
    simpa [handledTag, found] using (check_exact _ _ _).mpr valid

theorem rejected_tag_retains_full_payload (defaults : D → Domain) (arms : List (Arm F D))
    (row : VariantRow) (tag : Nat) (payload : Domain)
    (present : Variants.Merged.lookup tag row = some payload)
    (rejected : check defaults arms (.variant tag payload) = false) :
    Variants.Merged.lookup tag (residual defaults arms row) = some payload ∧
      (residual defaults arms row).entries ≠ [] := by
  have kept : Variants.Merged.lookup tag (residual defaults arms row) = some payload := by
    simp [residual_lookup, present, rejected]
  exact ⟨kept, List.ne_nil_of_mem ((Variants.Merged.mem_iff_lookup tag payload _).mpr kept)⟩

namespace Examples

def noDefaults : Empty → Domain := Empty.elim

def booleanArms : List (Arm Empty Empty) :=
  [⟨.literal (.bool false), false⟩, ⟨.literal (.bool true), false⟩]

theorem booleans_exhaustive : check noDefaults booleanArms (.base .bool) = true := rfl

theorem guarded_wildcard_not_counted :
    check (F := Empty) noDefaults [⟨.wildcard, true⟩] (.base .bool) = false := rfl

def tupleArms : List (Arm Empty Empty) :=
  [⟨.pair (.literal (.bool false)) .wildcard, false⟩,
   ⟨.pair (.literal (.bool true)) (.literal .unit), false⟩]

theorem tuple_product_exhaustive :
    check noDefaults tupleArms (.pair (.base .bool) (.base .unit)) = true := rfl

def listArms : List (Arm Empty Empty) := [⟨.nil, false⟩, ⟨.cons .wildcard .wildcard, false⟩]

theorem nil_cons_exhaustive (element : Domain) : check noDefaults listArms (.list element) = true := by
  simp [check, cells, listArms, checkOne, List.all_flatMap, List.all_map]

/-- Two payload tests in separate arms do not authorize subtraction of a
merged tag. This deliberately does not settle all source matrix rules. -/
theorem partial_payload_arms_do_not_remove_tag :
    check (F := Empty) noDefaults
      [⟨.variant 0 (.literal (.bool false)), false⟩,
       ⟨.variant 0 (.literal (.bool true)), false⟩]
      (.variant 0 (.base .bool)) = false := rfl

theorem merged_union_retained_after_partial_arm :
    let row := Variants.Merged.normalize Domain.union [(0, .base .int), (0, .base .str)]
    let arms : List (Arm Empty Empty) := [⟨.variant 0 (.literal (.int 0)), false⟩]
    (residual noDefaults arms row).entries = [(0, .union (.base .int) (.base .str))] := rfl

theorem merged_union_covered_by_whole_payload :
    let row := Variants.Merged.normalize Domain.union [(0, .base .int), (0, .base .str)]
    checkVariants (F := Empty) noDefaults [⟨.variant 0 .wildcard, false⟩] row = true := rfl

end Examples
end Yulang.CaseCoverage
