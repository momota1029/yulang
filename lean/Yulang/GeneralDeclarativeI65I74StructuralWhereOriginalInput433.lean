import Yulang.GeneralDeclarativeI65I74StructuralWherePairBindings433

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65
open GeneralDeclarations (Clause DeclarationChecked)
open GeneralDeclarativeSourceEmission322 (demand inputs useArg)
open GeneralDeclarativeWhere319 (Capture)
open Checker408 (Problem)

/-- A literal where variable of a checked declaration always uses
the actual captured head input. In this branch an arbitrary fallback
used for complex arguments is never consulted, and the shared
output-only binder is not needed to read the where input. -/
theorem literal_checked_where_use_reads_actual_parent_capture433
    {s : GeneralDeclarativeI65.State} {q : Request} (f : AuthoredBodyFrame393 s q)
    {ctors roles} (checked : DeclarationChecked ctors roles f.decl)
    {clause : Clause} {name : Nat} (used : clause ∈ f.decl.requirements)
    (original : clause.arguments = [.var name]) :
    (f.whereFor clause).demand.arguments = [f.input name] := by
  have hit : (.var name : GeneralDeclarationPatterns.Pattern) ∈ clause.arguments := by
    simp [original]
  have use : useArg f.names (f.placement.compound clause 0) (.var name) = f.input name :=
    GeneralDeclarativeProducedNames325.exact_clause_input checked used hit rfl
  simp only [AuthoredBodyFrame393.whereFor,demand,original,inputs]
  rw [use]

/-- In an accepted one-child packet the original request uses the
parent's actual captured head variable, not the B6 result, the child's
placement suggestion or an arbitrary fallback. -/
theorem original_wrap_child_uses_the_true_parent_capture433
    {p : Problem} (o : ReadAssociatedWrap432 p) :
    o.original.origin.child.demand.arguments = [o.event.frame.input o.original.headBinder] := by
  let f := o.event.frame
  have here := original_where_clause_position399 o.original.origin
  have entry : o.original.origin.entry = f.whereFor o.original.origin.entry.clause := by
    have row := o.original.origin.atClause
    simpa [f,AuthoredBodyFrame393.clauses,here] using row.symm
  change o.original.origin.entry.demand.arguments = _
  rw [entry]
  exact literal_checked_where_use_reads_actual_parent_capture433 f
    (o.original.checked.2 _ (List.mem_of_getElem? f.authored)) (List.mem_of_getElem? here)
    o.original.independentInput

/-- A genuine two-child scoped reader has the same original captured
anonymous input at both clauses, although each writes its own declared
associated output at the shared fixed target. -/
theorem original_two_child_inputs_do_not_use_the_shared_output433
    {p : Problem} (o : ReadTwoNamedWrap433 p) :
    o.original.origin.child.demand.arguments = [o.event.frame.input o.original.headName] ∧
    o.secondRequest.demand.arguments = [o.event.frame.input o.original.headName] := by
  let f := o.event.frame
  have here := original_where_clause_position399 o.original.origin
  have entry : o.original.origin.entry = f.whereFor o.original.origin.entry.clause := by
    have row := o.original.origin.atClause
    simpa [f,AuthoredBodyFrame393.clauses,here] using row.symm
  have checked := o.original.checked.2 _ (List.mem_of_getElem? f.authored)
  constructor
  · change o.original.origin.entry.demand.arguments = _
    rw [entry]
    exact literal_checked_where_use_reads_actual_parent_capture433 f checked (List.mem_of_getElem? here)
      o.original.producerInput
  · change (f.whereFor o.original.sibling).demand.arguments = _
    have member : o.original.sibling ∈ f.decl.requirements := by
      rw [o.original.exactlyTwo]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    exact literal_checked_where_use_reads_actual_parent_capture433 f checked member o.original.siblingInput

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
