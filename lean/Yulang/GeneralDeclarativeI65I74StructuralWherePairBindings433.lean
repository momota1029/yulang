import Yulang.GeneralDeclarativeI65I74StructuralWherePairTrace433

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65
open Checker408 (Problem)

/-- The read-only two-child certificate is not choosing two unrelated
equal values. Both retained writes name the exact same original
physical output slot, with the distinct names and occurrences of
the two original lexical requests, before reading a fitted model. -/
theorem two_child_packet_retains_exact_original_output_bindings433
    {p : Problem} (o : ReadTwoNamedWrap433 p) :
    o.first.retained.write.occurrence = p.root.occurrence ++ [0] ∧
    o.second.retained.write.occurrence = p.root.occurrence ++ [1] ∧
    o.first.retained.write.outputOrdinal = 0 ∧ o.second.retained.write.outputOrdinal = 0 ∧
    o.first.retained.write.target = o.original.origin.output ∧
    o.second.retained.write.target.name = o.original.siblingOutput.name ∧
    o.second.retained.write.target.target = o.original.origin.output.target := by
  have secondClause : o.event.frame.decl.requirements[1]? = some o.original.sibling := by
    rw [o.original.exactlyTwo]
    rfl
  have secondEq : o.original.sibling.outputs[0]? = some o.original.siblingOutput := by
    rw [o.original.siblingOutputAt]
    rfl
  obtain ⟨named,_,namedAt,namedKey,namedTarget⟩ :=
    original_sibling_named_output_uses_parent_target432 o.event.frame o.original.declared
      secondClause secondEq o.original.siblingValue
  have placed := original_binder_reserves_the_named_shared_target432 o.original.origin o.original.declared
  have firstItem : o.first.retained.write.target = o.original.origin.output := by
    change o.original.origin.child.demand.outputs[
      ExplicitPick419.exactlyOneOutput ⟨p.state,o.original.origin.child⟩ o.first.single] = _
    have io := ExplicitPick419.one_output_is_zero419
      ⟨p.state,o.original.origin.child⟩ o.first.single o.original.origin.outputIndex
    exact (congrArg
      (fun i : Fin o.original.origin.child.demand.outputs.length => o.original.origin.child.demand.outputs[i])
      io.symm).trans (List.getElem?_eq_some_iff.mp o.original.origin.outputAt).2
  have secondItem : o.second.retained.write.target = named := by
    change o.secondRequest.demand.outputs[
      ExplicitPick419.exactlyOneOutput ⟨p.state,o.secondRequest⟩ o.second.single] = _
    have atIndex : o.secondRequest.demand.outputs[0]? = some named := namedAt
    exact (List.getElem?_eq_some_iff.mp atIndex).2
  refine ⟨?_,rfl,rfl,rfl,firstItem,?_,?_⟩
  · change p.root.occurrence ++ [o.original.origin.clauseOrdinal] = _
    rw [o.original.inOrder]
  · rw [secondItem,namedKey]
  · rw [secondItem,namedTarget,placed]

/-- In this narrow decoder the fixed target has a uniquely retained
literal RHS. Independent successful child reads of that target agree
on the actual retained syntax, stronger than model agreement; this
does not add a restriction to the declarative language. -/
theorem two_child_same_fixed_slot_has_same_retained_literal433
    {p : Problem} (o : ReadTwoNamedWrap433 p) :
    o.first.retained.expr = o.second.retained.expr := by
  have exactTargets := two_child_packet_retains_exact_original_output_bindings433 o
  have same : o.second.retained.write.target.target = o.first.retained.write.target.target := by
    rw [exactTargets.2.2.2.2.1,exactTargets.2.2.2.2.2.2]
  exact (o.first.retained.noOtherLiteral
    ⟨o.second.retained.write.target.target,o.second.retained.expr⟩ o.second.retained.atRow same).symm

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
