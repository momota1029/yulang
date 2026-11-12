import Yulang.GeneralNominalCycleDescent

/-! Paterson descent from an explicit finite-pattern readback correspondence.
The premise ties declaration keys, roles, emitted identities and finite labels
to actual selection, but does not yet prove the labels denote the captures. Its
producer and semantic adequacy for arbitrary
normalized inspection reports is still a source bridge to construct; cycles
captured without inspection must be represented by opaque finite leaves. -/
namespace Yulang.GeneralNominalCycleReadback

open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCycleK2

structure Readback (roles : Roles.RoleDecls) (registry : Registry) (context : GeneralNominalCandidates.Context) where
  lower : Occurrence roles → List Pattern
  upper : Occurrence roles → List Pattern
  selected : ∀ parent key children, Local registry context parent (.selected key children) →
    ∀ child ∈ children, ∃ declaration ∈ registry.declarations,
      ∃ checked : DeclarationChecked registry.constructors roles declaration,
        declaration.id = key ∧ declaration.role = parent.demand.role ∧
      ∃ bounds, GeneralNominalRecursiveCandidates.arguments context parent = some bounds ∧
        child ∈ GeneralNominalAllocation.children context.state registry parent declaration checked
          (GeneralNominalRecursiveInspection.bindings context.state
            (GeneralNominalRecursiveCandidates.report context declaration bounds)) ∧
      ∃ clause ∈ declaration.requirements,
        child.identity = GeneralNominalAllocation.source context.state registry parent.identity
          (GeneralNominalAllocation.origin parent.identity declaration.id 6 clause.id 0) ∧
      ∃ lo hi : Nat → Pattern,
        lower parent = substArgs lo declaration.head ∧ upper parent = substArgs hi declaration.head ∧
        lower child = substArgs lo clause.arguments ∧ upper child = substArgs hi clause.arguments

def weight (readback : Readback roles registry context) (root : Occurrence roles) : Nat :=
  Roles.argsSize (counted (readback.lower root)) + Roles.argsSize (counted (readback.upper root))

theorem child_decreases (checked : Checked registry) (readback : Readback roles registry context)
    (parent child : Occurrence roles)
    (edge : CommonRoleOutermostResolver.Child (Local registry context) child parent) :
    weight readback child < weight readback parent := by
  obtain ⟨key,children,selected,member⟩ := edge
  obtain ⟨declaration,visible,_,_,_,_,_,_,clause,present,_,lo,hi,a,b,c,d⟩ := readback.selected parent key children selected child member
  have lower := ((checked.2 declaration visible).captureStable clause present lo).1
  have upper := ((checked.2 declaration visible).captureStable clause present hi).1
  unfold weight
  rw [a,b,c,d]
  exact Nat.add_lt_add lower upper

theorem whereAccessible (checked : Checked registry) (readback : Readback roles registry context) (root : Occurrence roles) :
    Acc (CommonRoleOutermostResolver.Child (Local registry context)) root := by
  induction root using (measure (weight readback)).wf.induction with
  | h root ih =>
    refine Acc.intro root ?_
    intro child edge
    exact ih child (child_decreases checked readback root child edge)

end Yulang.GeneralNominalCycleReadback
