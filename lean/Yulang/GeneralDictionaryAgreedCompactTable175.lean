import Yulang.GeneralDictionaryAgreedTable175

/-! Remove duplicate role entries from the shared height table. The original
uniform fuel is retained, so this changes storage/recomputation only, not the
certificate bound or its restricted role-DAG meaning. The role inventory is
computed once and passed unchanged through all rounds. -/
namespace Yulang.GeneralDictionaryAgreedCompactTable175
open GeneralDeclarations GeneralDictionaryAgreedComputed174
open GeneralDictionaryAgreedUniform174 GeneralDictionaryAgreedEdge174
open GeneralDictionaryAgreedTable175

def compactNodes (registry : Registry) : List Nat := (roleNodes registry).eraseDups

def advanceOn (registry : Registry) (nodes : List Nat) (old : Table) : Table :=
  nodes.map fun role => (role,
    (childRoles registry role).foldl
      (fun height child => max height (lookup old child + 1)) 0)

/-- `nodes` is fixed across all rounds, not reconstructed on recursion. -/
def tableOn (registry : Registry) (nodes : List Nat) : Nat → Table
  | 0 => []
  | fuel + 1 => advanceOn registry nodes (tableOn registry nodes fuel)

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

/-- Any inventory covering all declared parent/child roles is adequate.
It may reorder or duplicate entries; no semantic checking is assumed. -/
theorem tableOn_correct (registry : Registry) (nodes : List Nat)
    (covers : ∀ role ∈ roleNodes registry, role ∈ nodes)
    (fuel : Nat) (present : role ∈ roleNodes registry) :
    lookup (tableOn registry nodes fuel) role = computedHeight registry fuel role := by
  induction fuel generalizing role with
  | zero => rfl
  | succ fuel ih =>
    unfold tableOn advanceOn
    rw [lookup_map _ _ (covers role present)]
    unfold computedHeight
    apply fold_congr
    intro child member
    rw [ih (childRoles_mem_nodes member)]

theorem compactNodes_covers (present : role ∈ roleNodes registry) :
    role ∈ compactNodes registry := by
  simpa only [compactNodes,List.mem_eraseDups] using present

def compactHeight (registry : Registry) (fuel : Nat) : Table :=
  tableOn registry (compactNodes registry) fuel

theorem compactHeight_correct (registry : Registry) (fuel : Nat)
    (present : role ∈ roleNodes registry) :
    lookup (compactHeight registry fuel) role = computedHeight registry fuel role :=
  tableOn_correct registry _ (fun _ member => compactNodes_covers member) fuel present

def checkCompact (registry : Registry) (fuel : Nat) : Bool :=
  let table := compactHeight registry fuel
  registry.declarations.all fun declaration => declaration.requirements.all fun clause =>
    decide (lookup table clause.role < lookup table declaration.role)

theorem checkCompact_eq (registry : Registry) (fuel : Nat) :
    checkCompact registry fuel = checkTable registry fuel := by
  rw [checkTable_eq]
  have truth : checkCompact registry fuel = true ↔ check registry fuel = true := by
    simp only [checkCompact,check,List.all_eq_true,decide_eq_true_eq]
    constructor <;> intro checked declaration visible clause member
    · have bound := checked declaration visible clause member
      rw [compactHeight_correct registry fuel (child_mem_nodes visible member),
        compactHeight_correct registry fuel (parent_mem_nodes visible)] at bound
      exact bound
    · rw [compactHeight_correct registry fuel (child_mem_nodes visible member),
        compactHeight_correct registry fuel (parent_mem_nodes visible)]
      exact checked declaration visible clause member
  cases a : checkCompact registry fuel <;> cases b : check registry fuel <;> simp_all

/-- Deliberately retains the ORIGINAL fuel, not the compact inventory length. -/
def certifyCompact (registry : Registry) : Bool :=
  checkCompact registry (roleNodes registry).length

theorem certifyCompact_eq (registry : Registry) :
    certifyCompact registry = certifyTable registry := checkCompact_eq registry _

theorem certifyCompact_iff : certifyCompact registry = true ↔ ∃ rank, RoleStratified registry rank := by
  rw [certifyCompact_eq]
  exact certifyTable_iff

theorem certifyCompact_reorders (order : GeneralRegistryReordering.Reorders first last) :
    certifyCompact first = certifyCompact last := by
  rw [certifyCompact_eq,certifyCompact_eq]
  exact certifyTable_reorders order

theorem tableOn_length (registry : Registry) (nodes : List Nat) (fuel : Nat) :
    (tableOn registry nodes (fuel+1)).length = nodes.length := by
  simp only [tableOn,advanceOn,List.length_map]

theorem compactHeight_length (registry : Registry) (fuel : Nat) :
    (compactHeight registry (fuel+1)).length = (compactNodes registry).length :=
  tableOn_length registry _ fuel

end Yulang.GeneralDictionaryAgreedCompactTable175
