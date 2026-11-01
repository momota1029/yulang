import YulangClosure.OriginalEffectHygiene
import YulangClosure.FormalPermissionSourceOrigin

/-!
R136 structural inventory for the committed nested formal constructor.
Source baseline abbe733b952138b5d576c30936692dd262f3e92f:
candidate_effect.rs candidate_formal_value_pair/candidate_formal_effect_port;
candidate_source.rs preflight_formal/preflight_formal_value.

The fragment contains scalar/variable/hole leaves, Functions and nonempty
Tuples whose immediate children have no effect annotation. Identifiers use
the existing Nat encoding; authentic HIR decoding is still an obligation.
Rows retain their original concrete sequence and symbolic variables separately.
This is a successful structural constructor law, not a native execution,
source interpretation instance, consumer/arrival law or subtraction theorem.
OriginalEffectHygiene's publication/receipt results do not supply those gaps.
-/
namespace YulangClosure.FormalPermissionConstructorR136

open FormalPermissionCaptureConstruction (Metadata)

abbrev PortStep := FormalPermissionCaptureConstruction.Step
open FormalPermissionSourceOrigin (Context)

structure Row where
  position : Nat
  concrete : List Nat
  variables : List Nat
  deriving DecidableEq, Repr

mutual
  inductive Value where
    | leaf
    | function (argument : Value) (argumentEffects : Option Row)
        (result : Value) (resultEffects : Option Row)
    | tuple (elements : Elements)
  inductive Elements where
    | nil
    | cons (head : Value) (tail : Elements)
end

structure LocatedPort where
  positive : Bool
  path : List PortStep
  row : Option Row

structure Permission where
  metadata : Metadata
  path : List PortStep
  deriving DecidableEq, Repr

def record (c : Context) (path : List PortStep) (row : Row) : Permission :=
  ⟨c.metadata row.position row.concrete, path⟩

def emit (c : Context) (port : LocatedPort) : List Permission :=
  match port.row with
  | none => []
  | some row =>
      if port.positive = false ∧ row.concrete ≠ [] ∧ row.variables = [] then
        [record c port.path row]
      else []

def rowAllowed (positive : Bool) : Option Row → Bool
  | none => true
  | some row => if positive then row.variables.length ≤ 1 else
      (row.concrete.isEmpty && row.variables.length == 1) ||
        (!row.concrete.isEmpty && row.variables.isEmpty)

mutual
  def supported : Value → Bool → Bool
    | .leaf, _ => true
    | .function a ae r re, p =>
        rowAllowed (!p) ae && supported a (!p) && rowAllowed p re && supported r p
    | .tuple .nil, _ => false
    | .tuple es@(.cons _ _), p => supportedElements es p
  def supportedElements : Elements → Bool → Bool
    | .nil, _ => true
    | .cons a rest, p => supported a p && supportedElements rest p
end

/- The independent port inventory includes every Function port, including
positive, omitted and symbolic ports. Tuples only move structural paths. -/
mutual
  def ports : Value → Bool → List PortStep → List LocatedPort
    | .leaf, _, _ => []
    | .function a ae r re, p, path =>
        ports a (!p) (path ++ [.argument]) ++ ports r p (path ++ [.result]) ++
          [⟨!p, path ++ [.argument], ae⟩, ⟨p, path ++ [.result], re⟩]
    | .tuple es, p, path => elementPorts es p path 0
  def elementPorts : Elements → Bool → List PortStep → Nat → List LocatedPort
    | .nil, _, _, _ => []
    | .cons a rest, p, path, i =>
        ports a p (path ++ [.element i]) ++ elementPorts rest p path (i + 1)
end

/- This traversal follows the native append order: argument value, result
value, immediate argument effect, immediate result effect. -/
mutual
  def inventory (c : Context) : Value → Bool → List PortStep → List Permission
    | .leaf, _, _ => []
    | .function a ae r re, p, path =>
        inventory c a (!p) (path ++ [.argument]) ++
          inventory c r p (path ++ [.result]) ++
          emit c ⟨!p, path ++ [.argument], ae⟩ ++
          emit c ⟨p, path ++ [.result], re⟩
    | .tuple es, p, path => elementInventory c es p path 0
  def elementInventory (c : Context) : Elements → Bool → List PortStep → Nat → List Permission
    | .nil, _, _, _ => []
    | .cons a rest, p, path, i =>
        inventory c a p (path ++ [.element i]) ++
          elementInventory c rest p path (i + 1)
end

def construct (c : Context) (value : Value) (positive : Bool) : Option (List Permission) :=
  if supported value positive then some (inventory c value positive []) else none

mutual
  /-- Exact sequence equality, retaining multiplicity and source order. -/
  theorem inventory_exact (c : Context) (value : Value) (p : Bool) (path : List PortStep) :
      inventory c value p path = (ports value p path).flatMap (emit c) := by
    cases value with
    | leaf => rfl
    | function a ae r re =>
        simp only [inventory, ports, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, List.append_nil,
          inventory_exact c a (!p) (path ++ [.argument]),
          inventory_exact c r p (path ++ [.result]), List.append_assoc]
    | tuple es => exact element_inventory_exact c es p path 0
  theorem element_inventory_exact (c : Context) (es : Elements) (p : Bool)
      (path : List PortStep) (i : Nat) :
      elementInventory c es p path i = (elementPorts es p path i).flatMap (emit c) := by
    cases es with
    | nil => rfl
    | cons a rest =>
        simp only [elementInventory, elementPorts, List.flatMap_append,
          inventory_exact c a p (path ++ [.element i]),
          element_inventory_exact c rest p path (i + 1)]
end

theorem emit_exact (c : Context) (port : LocatedPort) (permission : Permission) :
    permission ∈ emit c port ↔ ∃ row, port.row = some row ∧
      port.positive = false ∧ row.concrete ≠ [] ∧ row.variables = [] ∧
      permission = record c port.path row := by
  cases h : port.row with
  | none => simp [emit, h]
  | some row =>
      by_cases allowed : port.positive = false ∧ row.concrete ≠ [] ∧ row.variables = []
      · simp [emit, h, allowed.1, allowed.2.1, allowed.2.2]
      · simp [emit, h, allowed]
        intro positive nonempty variables
        exact False.elim (allowed ⟨positive, nonempty, variables⟩)

/-- No omitted/positive/symbolic/mixed port fabricates a grant. Every retained
record is the exact source-context/row/path record of a negative concrete port. -/
theorem inventory_membership (c : Context) (value : Value) (p : Bool)
    (path : List PortStep) (permission : Permission) :
    permission ∈ inventory c value p path ↔
      ∃ port ∈ ports value p path, ∃ row, port.row = some row ∧
        port.positive = false ∧ row.concrete ≠ [] ∧ row.variables = [] ∧
        permission = record c port.path row := by
  rw [inventory_exact]
  simp only [List.mem_flatMap, emit_exact]

theorem constructor_inventory (c : Context) (value : Value) (p : Bool)
    (output : List Permission) :
    construct c value p = some output ↔
      supported value p = true ∧ output = (ports value p []).flatMap (emit c) := by
  cases h : supported value p <;> simp [construct, h, inventory_exact, eq_comm]

theorem record_identity (c : Context) (path : List PortStep) (row : Row) :
    (record c path row).metadata.parameter = c.parameter ∧
    (record c path row).metadata.occurrence = c.occurrence ∧
    (record c path row).metadata.owner = c.owner ∧
    (record c path row).metadata.scope = c.scope ∧
    (record c path row).path = path ∧
    (record c path row).metadata.sourceRow = row.position ∧
    (record c path row).metadata.concrete = row.concrete := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- HIR represents concrete atoms plus one symbolic tail. Nested negative
formal ports reject that row; the outer entry rule only bounds tail count. -/
theorem mixed_row_boundary (position atom tail : Nat) (rest : List Nat) :
    rowAllowed false (some ⟨position, atom :: rest, [tail]⟩) = false ∧
    rowAllowed true (some ⟨position, atom :: rest, [tail]⟩) = true := by
  simp [rowAllowed]

/-- Separate outer computation-entry record; no nested structural path exists
on this record. Authentic registration/formal/entry matching is still OPEN. -/
structure EntryPermission where
  registration : Nat
  formal : Nat
  metadata : Metadata
  annotationPosition : Nat
  entryEffect : Nat

def constructEntry (c : Context) (registration formal annotationPosition entry : Nat)
    (row : Row) : Option (List EntryPermission) :=
  if row.variables.length ≤ 1 then
    some (if row.concrete.isEmpty then [] else
      [⟨registration, formal, c.metadata row.position row.concrete, annotationPosition, entry⟩])
  else none

theorem entry_mixed_retained (c : Context) (registration formal annotationPosition entry
    position atom tail : Nat) (rest : List Nat) :
    constructEntry c registration formal annotationPosition entry
      ⟨position, atom :: rest, [tail]⟩ =
      some [⟨registration, formal, c.metadata position (atom :: rest), annotationPosition, entry⟩] := by
  simp [constructEntry]

end YulangClosure.FormalPermissionConstructorR136

set_option pp.fullNames true

#check @YulangClosure.FormalPermissionConstructorR136.inventory_exact
#print axioms YulangClosure.FormalPermissionConstructorR136.inventory_exact

#check @YulangClosure.FormalPermissionConstructorR136.element_inventory_exact
#print axioms YulangClosure.FormalPermissionConstructorR136.element_inventory_exact

#check @YulangClosure.FormalPermissionConstructorR136.emit_exact
#print axioms YulangClosure.FormalPermissionConstructorR136.emit_exact

#check @YulangClosure.FormalPermissionConstructorR136.inventory_membership
#print axioms YulangClosure.FormalPermissionConstructorR136.inventory_membership

#check @YulangClosure.FormalPermissionConstructorR136.constructor_inventory
#print axioms YulangClosure.FormalPermissionConstructorR136.constructor_inventory

#check @YulangClosure.FormalPermissionConstructorR136.record_identity
#print axioms YulangClosure.FormalPermissionConstructorR136.record_identity

#check @YulangClosure.FormalPermissionConstructorR136.mixed_row_boundary
#print axioms YulangClosure.FormalPermissionConstructorR136.mixed_row_boundary

#check @YulangClosure.FormalPermissionConstructorR136.entry_mixed_retained
#print axioms YulangClosure.FormalPermissionConstructorR136.entry_mixed_retained
