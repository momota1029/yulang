import Yulang.MethodResolutionLocality

/-!
# Operation counts for the existing selection resolver

This reference interpreter counts an entry to the selection dispatcher, one
visible-role lookup, one candidate equality comparison, and one visited
record-spine node as unit operations. `methodRef` is an external table query;
its implementation cost and the bit cost of IDs are not asserted to be one.
No timing measurements or asymptotic claims about the unfinished Rust solver
are inferred from these counts.

The instrumented functions compute both the actual result and the count.
Their values agree with `MethodResolution.resolve`, including early equality
failure, first-field-wins, duplicate imports, and all three selection results.
The schedule count is the sum of its actual local work, with no global rescan.
-/

namespace Yulang.MethodResolutionCost

open MethodResolution
open Methods (Selection)
open MethodResolutionLocality (Answers)

universe u v

def allEqualCount [DecidableEq α] (expected : α) : List α → Bool × Nat
  | [] => (true, 0)
  | first :: rest =>
      if first = expected then
        let tail := allEqualCount expected rest
        (tail.1, tail.2 + 1)
      else (false, 1)

theorem allEqualCount_value [DecidableEq α] (expected : α) (members : List α) :
    (allEqualCount expected members).1 = Methods.AllEqual members expected := by
  induction members with
  | nil => rfl
  | cons first rest ih =>
      by_cases same : first = expected <;> simp [allEqualCount, Methods.AllEqual, same, ih]

theorem allEqualCount_bound [DecidableEq α] (expected : α) (members : List α) :
    (allEqualCount expected members).2 ≤ members.length := by
  induction members with
  | nil => simp [allEqualCount]
  | cons first rest ih =>
      by_cases same : first = expected
      · simpa only [allEqualCount, same, ↓reduceIte, List.length_cons] using Nat.add_le_add_right ih 1
      · simp [allEqualCount, same]

def selectCount [DecidableEq α] : List α → Selection α × Nat
  | [] => (.missing, 0)
  | first :: rest =>
      let checked := allEqualCount first rest
      (if checked.1 then .unique first else .ambiguous, checked.2)

theorem selectCount_value [DecidableEq α] (members : List α) :
    (selectCount members).1 = Methods.select members := by
  cases members <;> simp only [selectCount, Methods.select, allEqualCount_value]

theorem selectCount_bound [DecidableEq α] (members : List α) :
    (selectCount members).2 ≤ members.length := by
  cases members with
  | nil => simp [selectCount]
  | cons first rest =>
      exact Nat.le_trans (allEqualCount_bound first rest) (Nat.le_succ _)

def candidatesCount (scope : Scope) (name : Nat) : List Nat → List (Nat × Nat) × Nat
  | [] => ([], 0)
  | role :: rest =>
      let tail := candidatesCount scope name rest
      match scope.methodRef role name with
      | none => (tail.1, tail.2 + 1)
      | some declaration => ((role, declaration) :: tail.1, tail.2 + 1)

theorem candidatesCount_value (scope : Scope) (name : Nat) (roles : List Nat) :
    (candidatesCount scope name roles).1 =
      roles.filterMap (fun role => (scope.methodRef role name).map (role, ·)) := by
  induction roles with
  | nil => rfl
  | cons role rest ih =>
      cases found : scope.methodRef role name <;> simp [candidatesCount, found, ih]

theorem candidatesCount_steps (scope : Scope) (name : Nat) (roles : List Nat) :
    (candidatesCount scope name roles).2 = roles.length := by
  induction roles with
  | nil => rfl
  | cons role rest ih =>
      cases found : scope.methodRef role name <;> simp [candidatesCount, found, ih]

theorem candidatesCount_length (scope : Scope) (name : Nat) (roles : List Nat) :
    (candidatesCount scope name roles).1.length ≤ roles.length := by
  induction roles with
  | nil => simp [candidatesCount]
  | cons role rest ih =>
      cases found : scope.methodRef role name with
      | none => simpa only [candidatesCount, found, List.length_cons] using Nat.le_trans ih (Nat.le_succ _)
      | some declaration => simpa only [candidatesCount, found, List.length_cons] using Nat.add_le_add_right ih 1

def unknownCount (scope : Scope) (name : Nat) : Selection Reference × Nat :=
  let found := candidatesCount scope name scope.visibleRoles
  let selected := selectCount found.1
  let result := match selected.1 with
    | .missing => .unique (.field name)
    | .unique (role, declaration) => .unique (.role role declaration)
    | .ambiguous => .ambiguous
  (result, 1 + found.2 + selected.2)

theorem unknownCount_value (scope : Scope) (name : Nat) :
    (unknownCount scope name).1 = unknown scope name := by
  simp only [unknownCount, selectCount_value, candidatesCount_value, unknown, candidates]
  rfl

theorem unknownCount_bound (scope : Scope) (name : Nat) :
    (unknownCount scope name).2 ≤ 1 + 2 * scope.visibleRoles.length := by
  have selectBound := selectCount_bound (candidatesCount scope name scope.visibleRoles).1
  have lengthBound := candidatesCount_length scope name scope.visibleRoles
  simp only [unknownCount, candidatesCount_steps]
  omega

variable {Row : Type}

def typeNodes : StructuralBase.Ty Row → Nat
  | .base _ | .bottom | .top | .emptyRecord => 1
  | .union first last | .inter first last | .pair first last
  | .record _ first last | .arrow first _ last _ => 1 + typeNodes first + typeNodes last
  | .variant _ payload => 1 + typeNodes payload

def lookupCount (name : Nat) : StructuralBase.Ty Row → Option (StructuralBase.Ty Row) × Nat
  | .record label value rest =>
      if name = label then (some value, 1)
      else
        let tail := lookupCount name rest
        (tail.1, tail.2 + 1)
  | _ => (none, 1)

theorem lookupCount_value (name : Nat) (type : StructuralBase.Ty Row) :
    (lookupCount name type).1 = type.lookup name := by
  induction type with
  | record label value rest ihv ihr =>
      by_cases same : name = label <;> simp [lookupCount, StructuralBase.Ty.lookup, same, ihr]
  | _ => rfl

theorem lookupCount_bound (name : Nat) (type : StructuralBase.Ty Row) :
    (lookupCount name type).2 ≤ typeNodes type := by
  induction type with
  | record label value rest ihv ihr =>
      by_cases same : name = label
      · simp only [lookupCount, typeNodes, same, ↓reduceIte]
        omega
      · simp only [lookupCount, same, ↓reduceIte, typeNodes]
        omega
  | base | bottom | top | emptyRecord => exact Nat.le_refl _
  | union | inter | pair | variant | arrow => simp only [lookupCount, typeNodes]; omega

def knownCount (receiver : StructuralBase.Ty Row) (name : Nat)
    (fallback : Selection Nat) : Selection Reference × Nat :=
  let field := lookupCount name receiver
  let result := match field.1 with
    | some _ => .unique (.field name)
    | none => match fallback with
      | .missing => .missing
      | .unique declaration => .unique (.direct declaration)
      | .ambiguous => .ambiguous
  (result, 1 + field.2)

theorem knownCount_value (receiver : StructuralBase.Ty Row) (name : Nat) (fallback : Selection Nat) :
    (knownCount receiver name fallback).1 = known receiver name fallback := by
  simp only [knownCount, lookupCount_value, known]
  rfl

theorem knownCount_bound (receiver : StructuralBase.Ty Row) (name : Nat) (fallback : Selection Nat) :
    (knownCount receiver name fallback).2 ≤ 1 + typeNodes receiver :=
  Nat.add_le_add_left (lookupCount_bound name receiver) 1

def resolveCount (site : Site Row) : Selection Reference × Nat :=
  match site.receiver with
  | none => unknownCount site.scope site.name
  | some receiver => knownCount receiver site.name site.typedFallback

def siteBound (site : Site Row) : Nat :=
  match site.receiver with
  | none => 1 + 2 * site.scope.visibleRoles.length
  | some receiver => 1 + typeNodes receiver

/-- Counts are attached to a refinement of the actual resolver, not to an
unrelated successful path. Missing and ambiguous inputs are covered too. -/
theorem resolveCount_value (site : Site Row) : (resolveCount site).1 = resolve site := by
  cases receiver : site.receiver <;> simp [resolveCount, resolve, receiver, unknownCount_value, knownCount_value]

theorem resolveCount_bound (site : Site Row) : (resolveCount site).2 ≤ siteBound site := by
  cases receiver : site.receiver with
  | none => simpa only [resolveCount, siteBound, receiver] using unknownCount_bound site.scope site.name
  | some type => simpa only [resolveCount, siteBound, receiver] using knownCount_bound type site.name site.typedFallback

variable {SiteId : Type u} [DecidableEq SiteId]

def runCount (sites : SiteId → Site Row) : List SiteId → Answers SiteId → Answers SiteId × Nat
  | [], answers => (answers, 0)
  | site :: rest, answers =>
      let selected := resolveCount (sites site)
      let tail := runCount sites rest (fun current =>
        if current = site then some selected.1 else answers current)
      (tail.1, selected.2 + tail.2)

theorem runCount_value (sites : SiteId → Site Row) (order : List SiteId) (answers : Answers SiteId) :
    (runCount sites order answers).1 = MethodResolutionLocality.run sites order answers := by
  induction order generalizing answers with
  | nil => rfl
  | cons site rest ih =>
      simp only [runCount, ih, resolveCount_value,
        MethodResolutionLocality.run]
      rfl

theorem runCount_steps (sites : SiteId → Site Row) (order : List SiteId) (answers : Answers SiteId) :
    (runCount sites order answers).2 = (order.map fun site => (resolveCount (sites site)).2).sum := by
  induction order generalizing answers with
  | nil => rfl
  | cons site rest ih => simp only [runCount, ih, List.map_cons, List.sum_cons]

/-- The total cost is bounded by a function of the actual sizes of the
frozen input sites. Repeated schedule entries are counted again, not erased. -/
theorem runCount_bound (sites : SiteId → Site Row) (order : List SiteId) (answers : Answers SiteId) :
    (runCount sites order answers).2 ≤ (order.map fun site => siteBound (sites site)).sum := by
  induction order generalizing answers with
  | nil => exact Nat.le_refl _
  | cons site rest ih =>
      simp only [runCount, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (resolveCount_bound _) (ih _)

theorem runCount_uniform_bound (sites : SiteId → Site Row) (order : List SiteId)
    (answers : Answers SiteId) (bound : Nat)
    (bounded : ∀ site ∈ order, siteBound (sites site) ≤ bound) :
    (runCount sites order answers).2 ≤ order.length * bound := by
  induction order generalizing answers with
  | nil => simp [runCount]
  | cons site rest ih =>
      have here := Nat.le_trans (resolveCount_bound (sites site)) (bounded site (List.mem_cons_self))
      have later := ih
        (fun current => if current = site then some (resolveCount (sites site)).1 else answers current)
        (fun site member => bounded site (List.mem_cons_of_mem _ member))
      simp only [runCount, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

end Yulang.MethodResolutionCost
