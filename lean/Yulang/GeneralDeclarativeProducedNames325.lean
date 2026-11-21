import Yulang.GeneralDeclarativeEmissionForest322
import Yulang.GeneralPatternVariableProvenance
import Yulang.GeneralDeclarativeOutputIdentity324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProducedNames325
open GeneralDeclarations (Declaration DeclarationChecked OutputBinder)
open GeneralDeclarationPatterns (normalize variablesArgs normalizeArgs)
open GeneralPatternVariableProvenance (normalize_args_variables)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeSourceEmission322 (Names useOutput useArg)
open GeneralDeclarativeEmissionOutputs322 (Agree)
open GeneralDeclarativeOutputIdentity324 (direct_target)

def locate (binders : List OutputBinder) (placed : Nat → Nat → Nat) (n : Nat) : Option Nat :=
  match binders with
  | [] => none
  | b::more => if b.name = n then some (placed b.clause b.equation) else locate more placed n

theorem allocation_exact {bs : List OutputBinder} (nodup : (bs.map OutputBinder.name).Nodup)
    (member : b ∈ bs) : locate bs placed b.name = some (placed b.clause b.equation) := by
  induction bs with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl|later
    · simp [locate]
    · obtain ⟨distinct,inside⟩ := List.nodup_cons.mp nodup
      have notFirst : first.name ≠ b.name := fun h =>
        distinct (h ▸ (List.mem_map.mpr ⟨b,later,rfl⟩))
      simp [locate,notFirst,ih inside later]

def output (decl : Declaration) (placed : Nat → Nat → Nat) (n : Nat) : Nat :=
  (locate decl.outputBinders placed n).getD 0

def table (decl : Declaration) (placed : Nat → Nat → Nat) (resolved : Nat → Capture) : Names :=
  ⟨fun n => if n ∈ decl.outputNames then let u := output decl placed n; ⟨u,u,u⟩ else resolved n,
   output decl placed⟩

theorem exact_input (checked : DeclarationChecked c roles decl)
    (input : n ∈ decl.inputNames) : (table decl placed resolved).input n = resolved n := by
  have disjoint : n ∉ decl.outputNames :=
    fun only => checked.outputOnly.1 n only (normalize_args_variables decl.head input)
  simp [table,disjoint]

theorem enters_normal {ps : List GeneralDeclarationPatterns.Pattern} (bare : p ∈ ps)
    (asVariable : normalize p = .var n) :
    n ∈ variablesArgs (normalizeArgs ps) := by
  induction ps with
  | nil => cases bare
  | cons first rest ih =>
    rcases List.mem_cons.mp bare with rfl|inTail
    · simp [normalizeArgs,variablesArgs,asVariable,GeneralDeclarationPatterns.Pattern.variables]
    · exact List.mem_append_right _ (ih inTail)

theorem exact_clause_input (checked : DeclarationChecked c roles decl)
    (hasClause : clause ∈ decl.requirements) (bare : p ∈ clause.arguments)
    (asVariable : normalize p = .var n) :
    useArg (table decl placed resolved) fallback p = resolved n := by
  rw [GeneralDeclarativeSourceEmission322.source_var _ _ _ asVariable]
  exact exact_input checked (checked.scope.1 _ hasClause _ (enters_normal bare asVariable))

theorem coherent (decl : Declaration) (placed : Nat → Nat → Nat) (resolved : Nat → Capture) :
    Agree decl (table decl placed resolved) := by
  intro n out
  simp [table,out]

/-- The source's producing clause and equation select the logical name,
rather than a coincidentally equal associated key in another clause. -/
theorem generated (checked : DeclarationChecked c roles decl)
    (declared : binder ∈ decl.outputBinders) :
    ∃ cl ∈ decl.requirements, cl.id = binder.clause ∧
      ∃ eq ∈ cl.outputs, eq.id = binder.equation ∧
        (useOutput decl (table decl placed resolved) (placed cl.id) eq).target = placed cl.id eq.id := by
  obtain ⟨cl,inDecl,clId,eq,inClause,eqId,body⟩ := checked.produced binder declared
  have used : binder.name ∈ decl.outputNames := List.mem_map.mpr ⟨binder,declared,rfl⟩
  have read := direct_target (allocate := placed cl.id) (table decl placed resolved) body used
  refine ⟨cl,inDecl,clId,eq,inClause,eqId,?_⟩
  rw [read]
  simp only [table,output,allocation_exact checked.identified.2.2.2.1 declared,Option.getD_some,clId,eqId]

end Yulang.GeneralDeclarativeProducedNames325
