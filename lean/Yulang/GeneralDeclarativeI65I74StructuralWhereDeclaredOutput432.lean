import Yulang.GeneralDeclarativeI65I74StructuralWhereSelectedReceipt432
import Yulang.GeneralDeclarativeI65B6SameWhereProjections400

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere428
open GeneralDeclarations (OutputBinder Equation DeclarationChecked)
open GeneralDeclarationPatterns (Pattern variablesArgs)
open CommonDeclaredNominalInspection (Kind Parameter)
open CommonRecursiveNominalIntervals (effectiveParameter)
open CommonNominalFullCarrier (Ty Equivalent nominal)
open CommonRoleOutermostResolver (Tree)
open GeneralDeclarativeWitnessConstructorModes357 (Use)

/-- Exactly one authored **invariant value** argument. Constructor
identity, kind, effective variance and the actual mode table are data
from the source, not an assumption about what the spelling denotes. -/
def invariantUnaryValuePlan432 {s : GeneralDeclarativeI65.State}
    (ctor binder : Nat) (param : Parameter)
    (use : Use s.current.environment ctor 1)
    (names : GeneralDeclarativeWitnessSparseIntervals357.names use.mode 1 = some [param])
    (declared : s.modes[ctor]? = some [param])
    (kind : param.kind = .value)
    (invariant : (effectiveParameter false param).variance = .invariant) :
    B6MixedRhs401 s false (.app ctor [.var binder]) :=
  .declaredApp ctor use names declared (.cons (.valueInterval binder kind invariant ()) .nil)

theorem invariant_unary_RHS_reads_the_declared_where_slot432
    {s q f} {binder : OutputBinder} {body : Equation}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    {ctor : Nat} {param : Parameter} {use : Use s.current.environment ctor 1}
    {names declared kind invariant} (m : GeneralDeclarativeI65.Model) :
    evaluateMixedRhs401 (sourceRead401 m (f.slots (.explicit body)))
      (invariantUnaryValuePlan432 ctor binder.name param use names declared kind invariant) =
    some (nominal ctor [.inl (m.assignment origin.output.target).1]) := by
  simp [invariantUnaryValuePlan432,evaluateMixedRhs401,evaluateMixedArgs401,evaluateMixedArg401,
    sourceRead401,origin.slot]

private theorem evaluate_mixed_plan_heq432 {s c p p'} {x : B6MixedRhs401 s c p}
    {y : B6MixedRhs401 s c p'}
    (read : ∀ _k _n, Unit → Option (Ty × Common.Row)) (indexed : p = p') (same : HEq x y) :
    evaluateMixedRhs401 read x = evaluateMixedRhs401 read y := by
  subst p'
  rw [eq_of_heq same]

/-- The fixed receipt of an *actually selected original parent* evaluates
its typed unary RHS at the source where slot. The typed plan equating
its original B6 instance to this typedPattern is an explicit prerequisite,
not synthesized from receipt/dictionary equality or fitted values.
This theorem does not promote a parent with an absent B6 plan. -/
theorem actual_parent_unary_output_uses_exact_where_target432
    {R : SourcePrimitives} (law : SelectedLaw428 R)
    {s : I72.State} {q : Request} {t : Tree} {e : Event s q}
    (selected : SourceTrace R s q t (some e))
    {binder : OutputBinder} {body : Equation}
    (origin : OriginalWhereBinder395 e.frame binder body)
    (out : Fin q.demand.outputs.length)
    (sameBody : (e.outputs out).body = .explicit body)
    {ctor : Nat} {param : Parameter} {use : Use s.core.current.environment ctor 1}
    {names declared kind invariant}
    (sourceSyntax : GeneralDeclarationPatterns.normalize
      (GeneralDeclarativeOutputs320.bodyPattern (e.outputs out).body) = .app ctor [.var binder.name])
    (typedShape : HEq (e.outputs out).plan
      (invariantUnaryValuePlan432 ctor binder.name param use names declared kind invariant))
    (m : I72.Model) (fit : I72.Fits s m) :
    (e.outputs out).receipt.actualEquation m =
      some (q.demand.outputs[out].target,
        nominal ctor [.inl (m.assignment origin.output.target).1]) ∧
    Equivalent (m.assignment q.demand.outputs[out].target).1
      (nominal ctor [.inl (m.assignment origin.output.target).1]) := by
  have localFacts : LocalMeaning m e ∧ FixedTargets m e := by
    cases selected with
    | selected _ _ picked _ _ => exact law picked m fit
  have exactEval := evaluate_mixed_plan_heq432
    (sourceRead401 m (e.frame.slots (.explicit body))) sourceSyntax typedShape
  rw [invariant_unary_RHS_reads_the_declared_where_slot432 origin m] at exactEval
  obtain ⟨_,_,_,_,_,v,receipt,evaluated⟩ := localFacts.1.rhs out
  have sameSlots := congrArg (fun b => sourceRead401 m (e.frame.slots b)) sameBody
  rw [sameSlots,exactEval] at evaluated
  have vExact := Option.some.inj evaluated
  rw [← vExact] at receipt
  refine ⟨receipt,?_⟩
  obtain ⟨w,stored,agrees⟩ := localFacts.2 out
  have values := congrArg Prod.snd (Option.some.inj (stored.symm.trans receipt))
  change w = nominal ctor [.inl (m.assignment origin.output.target).1] at values
  rw [← values]
  exact agrees

/-- The real declaration boundary still forbids an output-only binder
from being used as an anonymous input to **any** where child, even in
an erased syntactic branch. This is not a new rejection rule. -/
theorem original_output_binder_cannot_be_where_input432 {s q f}
    {binder : OutputBinder} {body : Equation}
    (_ : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    {constructors roles} (checked : DeclarationChecked constructors roles f.decl)
    (bound : binder ∈ f.decl.outputBinders) {clause} (fromSource : clause ∈ f.decl.requirements) :
    binder.name ∉ variablesArgs clause.arguments :=
  checked.outputOnly.2 clause fromSource binder.name (List.mem_map.mpr ⟨binder,bound,rfl⟩)


/-- The source's original B6 read identifies the typed unary plan. The
constructor cannot be inferred from a semantically equal output value. -/
theorem original_atlas_read_recovers_typed_plan432
    {s : I72.State} {q : Request} {e : Event s q}
    (out : Fin q.demand.outputs.length)
    {typedPattern : Pattern}
    (shape : GeneralDeclarationPatterns.normalize
      (GeneralDeclarativeOutputs320.bodyPattern (e.outputs out).body) = typedPattern)
    (plan : B6MixedRhs401 s.core false typedPattern)
    (readOriginal : s.b6.read q e.frame.ordinal out (e.outputs out).body =
      some (cast (congrArg (B6MixedRhs401 s.core false) shape.symm) plan)) :
    HEq (e.outputs out).plan plan := by
  have eq := Option.some.inj ((e.outputs out).originalTyped.symm.trans readOriginal)
  exact (heq_of_eq eq).trans (cast_heq _ _)

open GeneralDeclarativeSourceEmission322 (useOutput)

/-- For a legal named associated-output equation, emitting the original
clause never turns the binder into an anonymous input. The output target
is fixed by the parent's authored output name, not the sibling's value. -/
theorem original_sibling_named_output_uses_parent_target432 {s q}
    (f : AuthoredBodyFrame393 s q) {binder : OutputBinder}
    (bound : binder ∈ f.decl.outputBinders) {clause : GeneralDeclarations.Clause}
    {whereOrdinal outputOrdinal : Nat} {equation : Equation}
    (atSource : f.decl.requirements[whereOrdinal]? = some clause)
    (atBody : clause.outputs[outputOrdinal]? = some equation)
    (literal : equation.rhs = .var binder.name) :
    ∃ requested : GeneralSourceState.Output,
      (frameWhereKids400 f)[whereOrdinal]? =
        some ⟨q.occurrence ++ [whereOrdinal],(f.whereFor clause).demand⟩ ∧
      (f.whereFor clause).demand.outputs[outputOrdinal]? = some requested ∧
      requested.name = equation.name ∧ requested.target = f.names.output binder.name := by
  let requested := useOutput f.decl f.names (f.placement.targets clause) equation
  have named : binder.name ∈ f.decl.outputNames := List.mem_map.mpr ⟨binder,bound,rfl⟩
  have here : (f.clauses.map LiteralWhereEntry.demand)[whereOrdinal]? =
      some (f.whereFor clause).demand := by
    simp [AuthoredBodyFrame393.clauses,atSource]
  refine ⟨requested,?_,?_,rfl,?_⟩
  · unfold frameWhereKids400 children
    rw [List.getElem?_map,List.getElem?_zipIdx]
    simp [here]
  · simp [requested,AuthoredBodyFrame393.whereFor,GeneralDeclarativeSourceEmission322.demand,atBody]
  · simp [requested,useOutput,GeneralDeclarationDemands.outputTarget,
      GeneralDeclarativeSourceEmission322.Names.old,literal,GeneralDeclarationPatterns.normalize,named]

/-- A producer's original output binder reservation is the very parent
target used by a sibling's allowed named output equation. Equal model
values, dictionary keys or sibling execution order are not involved. -/
theorem original_binder_reserves_the_named_shared_target432 {s q f}
    {binder : OutputBinder} {body : Equation}
    (origin : OriginalWhereBinder395 (s := s) (q := q) f binder body)
    (bound : binder ∈ f.decl.outputBinders) :
    origin.output.target = f.names.output binder.name := by
  have sourceIndex := original_where_clause_position399 origin
  obtain ⟨requested,_,atOutput,_,exact⟩ :=
    original_sibling_named_output_uses_parent_target432 f bound sourceIndex origin.atEquation origin.binderRhs
  have entry : origin.entry = f.whereFor origin.entry.clause := by
    have result := origin.atClause
    simpa [AuthoredBodyFrame393.clauses,sourceIndex] using result.symm
  have actual := origin.outputAt
  rw [entry] at actual
  rw [Option.some.inj (actual.symm.trans atOutput)]
  exact exact

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
