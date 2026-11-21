import Yulang.GeneralDeclarativeEvidence320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 3700000
namespace Yulang.GeneralDeclarativeNamedTree320
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarations (Registry Declaration Clause Equation)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand sourceValue)
open GeneralDeclarativeAssembly320 (Meaning ChildDenotes)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeOutputs320 (bodyCapture bodyPattern)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralSourceState (Output)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonRoleOutermostResolver (All₂ Dictionary)

theorem position {p : α → β → Prop} {xs : List α} {ys : List β}
    (ordered : All₂ p xs ys) {i : Nat} {a : α} {b : β}
    (left : xs[i]? = some a) (right : ys[i]? = some b) : p a b := by
  induction ordered generalizing i with
  | nil => cases left
  | cons first tail ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at left right
      cases left; cases right
      exact first
    | succ i => exact ih left right

/-- The request actually emitted at the specified source where position
has the meaning of its child's selected explicit/default associated
definition. Neither matching clauses nor matching requests by mere
membership would suffice in the presence of duplicates. -/
theorem linked_output {r : Registry} {interp : Interpretation} {m : Assignment}
    {parent : Demand} {decl : Declaration} {capture : Nat → Capture}
    {children : List Demand} {dicts : List Dictionary}
    (root : Meaning r interp m parent decl capture children)
    (kids : All₂ (Evidence r interp m) children dicts)
    {i j : Nat} {clause : Clause} {child : Demand} {key : Nat} {tail : List Dictionary}
    {equation : Equation} {out : Output}
    (listed : decl.requirements[i]? = some clause)
    (generated : children[i]? = some child)
    (selected : dicts[i]? = some (.node key tail))
    (wrote : clause.outputs[j]? = some equation)
    (asked : child.outputs[j]? = some out) :
    ∃ childDecl childCapture body,
      childDecl.id = key ∧ childDecl ∈ r.declarations ∧ childDecl.role = clause.role ∧
      out.name = equation.name ∧ Supplies r.roles childDecl out.name body ∧
      Equivalent (sourceValue r.constructors interp capture m equation.rhs)
        (sourceValue r.constructors interp (bodyCapture child childCapture body) m (bodyPattern body)) := by
  have parents := position root.children listed generated
  have po := position parents.outputs wrote asked
  have found : out ∈ child.outputs := List.mem_of_getElem? asked
  have childSolved := position kids generated selected
  cases childSolved with
  | node node _ =>
    obtain ⟨choice,values,keyEq,certificate⟩ := node
    obtain ⟨body,supplied,denotes⟩ := certificate.outputs out found
    exact ⟨choice,values,body,keyEq,certificate.visible,certificate.role.trans parents.role,po.1,supplied,
      eqv_trans (eqv_symm po.2) denotes⟩

end Yulang.GeneralDeclarativeNamedTree320
