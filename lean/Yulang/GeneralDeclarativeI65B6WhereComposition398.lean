import Yulang.GeneralDeclarativeI65B6SymbolicSource398

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarations (Equation)

/-- A logical output of a supplied frame at the exact child request
site is consumed at the parent's original lexical where name.
Request identity alone does not link the frame's declaration to the
declaration selected by the finite proof. No equality of targets
from different occurrences is used. -/
theorem same_where_child_consumes_logical_output398 {s q f binder body rules dicts}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (forest : SelectedSourceForest383 rules s
      (children q (f.clauses.map LiteralWhereEntry.demand)) dicts)
    {childFrame : AuthoredBodyFrame393 s origin.child}
    (made : LogicalRoleOutput398 childFrame origin.outputIndex) :
    ∃ d : Dictionary, dicts[origin.clauseOrdinal]? = some d ∧
      Nonempty (SelectedSourceProof383 rules s origin.child d) ∧
      made.equation.occurrence = q.occurrence ++ [origin.clauseOrdinal] ∧
      made.equation.ordinal = origin.outputOrdinal ∧
      made.equation.requested = origin.output ∧
      f.slots (.explicit body) binder.name =
        some ⟨made.equation.requested.target,made.equation.requested.target,
          made.equation.requested.target⟩ := by
  let selected := selectWhereBinderProducer395 origin forest
  have same : made.equation.requested = origin.output :=
    (List.getElem?_eq_some_iff.mp origin.outputAt).2
  exact ⟨selected.dictionary,selected.dictionaryAt,selected.proof,rfl,rfl,same,by
    rw [same]; exact origin.slot⟩

/-- Carry out symbolic B4 output production at the actual ordered
where child rather than assume that child's output receipt.
The supplied source plan and its capture-kind compatibility are still
B6 data; the child's frame is not reconstructed from bare Classifies. -/
theorem supplied_where_child_produces_consumed_logical_output398 {s q f binder body rules dicts}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (forest : SelectedSourceForest383 rules s
      (children q (f.clauses.map LiteralWhereEntry.demand)) dicts)
    (childFrame : AuthoredBodyFrame393 s origin.child)
    (atlas : B6SymbolicAtlas398 s)
    (unique : (childFrame.decl.associated.map Equation.name).Nodup)
    {supplier : Body} (supplied : Supplies (authoredRegistry s.current).roles childFrame.decl
      origin.child.demand.outputs[origin.outputIndex].name supplier)
    {plan : B6ValuePlan398 s false (normalize (bodyPattern supplier))}
    (typed : atlas.read childFrame.ordinal supplier = some plan)
    (compatible : B6UsesFit398 s (childFrame.slots supplier) plan.needs) :
    ∃ out : LogicalRoleOutput398 childFrame origin.outputIndex,
      logicalOutputAt398 childFrame atlas origin.outputIndex unique = some out ∧
      out.body = supplier ∧
      CompoundSourceRhs394 s (childFrame.slots supplier) false
        (normalize (bodyPattern supplier)) out.equation.rhs ∧
      ∃ d : Dictionary, dicts[origin.clauseOrdinal]? = some d ∧
        Nonempty (SelectedSourceProof383 rules s origin.child d) ∧
        out.equation.occurrence = q.occurrence ++ [origin.clauseOrdinal] ∧
        out.equation.ordinal = origin.outputOrdinal ∧
        out.equation.requested = origin.output ∧
        f.slots (.explicit body) binder.name =
          some ⟨out.equation.requested.target,out.equation.requested.target,
            out.equation.requested.target⟩ := by
  obtain ⟨out,replayed,source,_,meaning⟩ :=
    supplied_symbolic_body_produces_exact_logical_output398
      childFrame atlas origin.outputIndex unique supplied typed compatible
  exact ⟨out,replayed,source,meaning,same_where_child_consumes_logical_output398 origin forest out⟩

end Yulang.GeneralDeclarativeI65
