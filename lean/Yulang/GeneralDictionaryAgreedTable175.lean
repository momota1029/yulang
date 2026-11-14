import Yulang.GeneralDictionaryAgreedUniform174

/-! A level-by-level table implementation of the role-DAG certificate.
It computes each listed role once per fuel level instead of expanding its
subtree separately for every incoming edge. Duplicate node names are harmless.
This recognizes the same restricted syntactic fragment as `certify`; failure
is not language rejection. No semantic rule or existing checker is changed. -/
namespace Yulang.GeneralDictionaryAgreedTable175
open GeneralDeclarations GeneralDictionaryAgreedComputed174
open GeneralDictionaryAgreedUniform174 GeneralDictionaryAgreedEdge174

abbrev Table := List (Nat × Nat)

def lookup : Table → Nat → Nat
  | [], _ => 0
  | (key,value) :: rest, role => if key = role then value else lookup rest role

def advance (registry : Registry) (old : Table) : Table :=
  (roleNodes registry).map fun role => (role,
    (childRoles registry role).foldl
      (fun height child => max height (lookup old child + 1)) 0)

/-- Each round is evaluated against the complete preceding table. -/
def heightTable (registry : Registry) : Nat → Table
  | 0 => []
  | fuel + 1 => advance registry (heightTable registry fuel)

theorem lookup_map (nodes : List Nat) (f : Nat → Nat) (present : role ∈ nodes) :
    lookup (nodes.map fun key => (key,f key)) role = f role := by
  induction nodes with
  | nil => cases present
  | cons key rest ih =>
    simp only [List.map_cons,lookup]
    split
    next same => exact congrArg f same
    next different =>
      apply ih
      rcases List.mem_cons.mp present with same | member
      · exact False.elim (different same.symm)
      · exact member

private theorem fold_congr (nodes : List Nat) (f g : Nat → Nat)
    (same : ∀ key ∈ nodes, f key = g key) (initial : Nat) :
    nodes.foldl (fun h key => max h (f key)) initial =
      nodes.foldl (fun h key => max h (g key)) initial := by
  induction nodes generalizing initial with
  | nil => rfl
  | cons key rest ih =>
    simp only [List.foldl_cons]
    rw [same key (by simp)]
    exact ih (fun k mem => same k (by simp [mem])) _

theorem parent_mem_nodes (visible : declaration ∈ registry.declarations) :
    declaration.role ∈ roleNodes registry := by
  exact List.mem_flatMap.mpr ⟨declaration,visible,List.mem_cons_self ..⟩

theorem childRoles_mem_nodes (present : child ∈ childRoles registry role) :
    child ∈ roleNodes registry := by
  obtain ⟨declaration,visible,_,clause,member,same⟩ := mem_childRoles.mp present
  exact same ▸ child_mem_nodes visible member

/-- Exact equality at every role used by a declaration or where clause,
for all fuel including zero. No acyclicity hypothesis is required. -/
theorem heightTable_correct (registry : Registry) (fuel : Nat)
    (present : role ∈ roleNodes registry) :
    lookup (heightTable registry fuel) role = computedHeight registry fuel role := by
  induction fuel generalizing role with
  | zero => rfl
  | succ fuel ih =>
    unfold heightTable advance
    rw [lookup_map _ _ present]
    unfold computedHeight
    apply fold_congr
    intro child member
    rw [ih (childRoles_mem_nodes member)]

/-- The height table is shared by every check of an actual declared edge. -/
def checkTable (registry : Registry) (fuel : Nat) : Bool :=
  let table := heightTable registry fuel
  registry.declarations.all fun declaration => declaration.requirements.all fun clause =>
    decide (lookup table clause.role < lookup table declaration.role)

theorem checkTable_eq (registry : Registry) (fuel : Nat) :
    checkTable registry fuel = check registry fuel := by
  have truth : checkTable registry fuel = true ↔ check registry fuel = true := by
    simp only [checkTable,check,List.all_eq_true,decide_eq_true_eq]
    constructor <;> intro checked declaration visible clause member
    · have bound := checked declaration visible clause member
      rw [heightTable_correct registry fuel (child_mem_nodes visible member),
        heightTable_correct registry fuel (parent_mem_nodes visible)] at bound
      exact bound
    · rw [heightTable_correct registry fuel (child_mem_nodes visible member),
        heightTable_correct registry fuel (parent_mem_nodes visible)]
      exact checked declaration visible clause member
  cases a : checkTable registry fuel <;> cases b : check registry fuel <;> simp_all

def certifyTable (registry : Registry) : Bool :=
  checkTable registry (roleNodes registry).length

theorem certifyTable_eq (registry : Registry) : certifyTable registry = certify registry :=
  checkTable_eq registry _

theorem certifyTable_iff : certifyTable registry = true ↔ ∃ rank, RoleStratified registry rank := by
  rw [certifyTable_eq]
  exact certify_iff

theorem certifyTable_reorders (order : GeneralRegistryReordering.Reorders first last) :
    certifyTable first = certifyTable last := by
  rw [certifyTable_eq,certifyTable_eq]
  exact certify_reorders order

theorem wrap_certified : certifyTable GeneralDictionaryAgreedRoleExamples174.wrapOnly = true := by
  rw [certifyTable_eq]
  exact GeneralDictionaryAgreedUniform174.wrap_certified

theorem recursive_not_certified : certifyTable GeneralDeclarationExamples.registry = false := by
  rw [certifyTable_eq]
  exact GeneralDictionaryAgreedUniform174.recursive_not_certified

end Yulang.GeneralDictionaryAgreedTable175
