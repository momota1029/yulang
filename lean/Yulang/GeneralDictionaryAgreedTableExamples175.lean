import Yulang.GeneralDictionaryAgreedTable175

/-! Boundary regressions for the table implementation. These synthetic
registries are not asserted Checked: duplicate declaration/clause identifiers
are deliberate, and certificate success is not declaration validity.
Disconnected cycles must still fail because certification checks all edges. -/
namespace Yulang.GeneralDictionaryAgreedTableExamples175
open GeneralDeclarations GeneralDeclarationExamples
open GeneralDictionaryAgreedTable175 GeneralDictionaryAgreedComputed174
open GeneralDictionaryAgreedUniform174 GeneralDictionaryAgreedEdge174

def declaration (parent : Nat) (children : List Nat) : Declaration :=
  { display with
    id := 7
    role := parent
    requirements := children.map fun role => {displayChild with id := 7, role := role} }

def graph (declarations : List Declaration) : Registry :=
  {registry with declarations := declarations}

def emptyGraph : Registry := graph []

def repeatedDAG : Registry := graph
  [declaration 10 [11,11], declaration 10 [11], declaration 11 []]

def disconnectedCycle : Registry := graph
  [declaration 10 [11], declaration 20 [21], declaration 21 [20]]

/-- Empty tables, zero fuel, and no declared edges are accepted. -/
theorem empty_all_fuel (fuel : Nat) : checkTable emptyGraph fuel = true := by
  rfl

theorem empty_certified : certifyTable emptyGraph = true := by rfl

/-- Repeated node names, edge multiplicity, and duplicate IDs do not change
height correctness. No uniqueness premise is secretly needed by the table. -/
theorem repeated_certified : certifyTable repeatedDAG = true := by decide +kernel

theorem repeated_zero_fails : checkTable repeatedDAG 0 = false := by decide +kernel

theorem repeated_one_passes : checkTable repeatedDAG 1 = true := by decide +kernel

/-- A cycle in a separate component cannot be ignored merely because the
first declaration belongs to an acyclic component. All fuel values fail. -/
theorem disconnected_all_fuel (fuel : Nat) : checkTable disconnectedCycle fuel = false := by
  cases result : checkTable disconnectedCycle fuel with
  | false => rfl
  | true =>
    have stratified := check_sound ((checkTable_eq disconnectedCycle fuel) ▸ result)
    have a := stratified (declaration 20 [21]) (by simp [disconnectedCycle,graph])
      {displayChild with id := 7, role := 21} (by simp [declaration])
    have b := stratified (declaration 21 [20]) (by simp [disconnectedCycle,graph])
      {displayChild with id := 7, role := 20} (by simp [declaration])
    exact False.elim (Nat.lt_asymm a b)

theorem disconnected_not_certified : certifyTable disconnectedCycle = false :=
  disconnected_all_fuel _

/-- Reverse both visible and where enumerations, preserving multiplicities. -/
def reverseGraph (source : Registry) : Registry :=
  {source with declarations := source.declarations.reverse.map fun declaration =>
    {declaration with requirements := declaration.requirements.reverse} }

theorem reverseGraph_reorders (source : Registry) :
    GeneralRegistryReordering.Reorders source (reverseGraph source) := by
  refine ⟨rfl,rfl,source.declarations.reverse,List.reverse_perm _ |>.symm,?_⟩
  change CommonRoleOutermostResolver.All₂ GeneralRegistryReordering.DeclarationReorders
    source.declarations.reverse (source.declarations.reverse.map _)
  induction source.declarations.reverse with
  | nil => exact .nil
  | cons d ds ih =>
    exact .cons ⟨rfl,rfl,rfl,(List.reverse_perm _).symm,rfl,rfl⟩ ih

theorem reverseGraph_certificate (source : Registry) :
    certifyTable source = certifyTable (reverseGraph source) :=
  certifyTable_reorders (reverseGraph_reorders source)

theorem reversed_cycle_not_certified : certifyTable (reverseGraph disconnectedCycle) = false := by
  rw [← reverseGraph_certificate]
  exact disconnected_not_certified

-- Executed smoke outputs supplement the proofs; they do not certify Checked.
#eval certifyTable emptyGraph
#eval certifyTable repeatedDAG
#eval certifyTable disconnectedCycle
#eval certifyTable (reverseGraph disconnectedCycle)

end Yulang.GeneralDictionaryAgreedTableExamples175
