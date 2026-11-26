import Yulang.GeneralDeclarativeI65I74StructuralWhereDeclaredOutput432

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
open GeneralDeclarativeI65 StructuralWhere428
open GeneralDeclarations (OutputBinder Equation Clause Checked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarationPatterns (Pattern)
open CommonDeclaredNominalInspection (Parameter)
open CommonRecursiveNominalIntervals (effectiveParameter)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open CommonRoleOutermostResolver (Tree Dictionary Summarizes)
open CommonNominalFullCarrier (Ty Equivalent subtype_trans)

/-- Unlike a binder origin, a later child's named output need not be
the declaration that introduced the binder. Its two original ordinals
still address a slot in the caller's actual where request, not a fresh
anonymous input or a slot guessed from fitted equality. -/
theorem selected_named_sibling_replays_same_fixed_target433
    {R : SourcePrimitives} (law : SelectedLaw428 R)
    {s : I72.State} {q : Request} {t : Tree} {parent : Event s q}
    (trace : SourceTrace R s q t (some parent))
    {key : Nat} {ds : List Dictionary} (summary : Summarizes t (.selected (.node key ds)))
    {binder : OutputBinder} {body : Equation}
    (origin : OriginalWhereBinder395 parent.frame binder body)
    (declared : binder ∈ parent.frame.decl.outputBinders)
    {clause : Clause} {siblingOrdinal siblingOutputOrdinal : Nat} {equation : Equation}
    (separate : siblingOrdinal ≠ origin.clauseOrdinal)
    (clauseAt : parent.frame.decl.requirements[siblingOrdinal]? = some clause)
    (writtenAt : clause.outputs[siblingOutputOrdinal]? = some equation)
    (namedOutput : equation.rhs = .var binder.name) :
    ∃ (prodTree siblingTree : Tree) (prodDict siblingDict : Dictionary)
      (prodEvent : Event s origin.child)
      (prodTrace : SourceTrace R s origin.child prodTree (some prodEvent))
      (sibling : Request) (sibEvent : Event s sibling)
      (sibTrace : SourceTrace R s sibling siblingTree (some sibEvent))
      (ix : Fin sibling.demand.outputs.length),
      ActualWhereTraceAt432 trace origin.clauseOrdinal prodTrace ∧
      ActualWhereTraceAt432 trace siblingOrdinal sibTrace ∧
      ds[origin.clauseOrdinal]? = some prodDict ∧ ds[siblingOrdinal]? = some siblingDict ∧
      sibling.occurrence = q.occurrence ++ [siblingOrdinal] ∧
      sibling.occurrence ≠ origin.child.occurrence ∧
      ix.val = siblingOutputOrdinal ∧
      sibling.demand.outputs[ix].name = equation.name ∧
      sibling.demand.outputs[ix].target = origin.output.target ∧
      (∀ m : I72.Model, Fits s m →
        DictionaryEvidence s m origin.child prodDict ∧ DictionaryEvidence s m sibling siblingDict ∧
        ∃ (prodValue sibValue : Ty),
          (prodEvent.outputs origin.outputIndex).receipt.actualEquation m =
            some (origin.output.target,prodValue) ∧
          (sibEvent.outputs ix).receipt.actualEquation m =
            some (origin.output.target,sibValue) ∧
          Equivalent prodValue sibValue) := by
  obtain ⟨pt,pd,pe,pSrc,pPos,pDict,_,_,_,_,_,pFacts⟩ :=
    actual_where_child_supplies_original_lexical_output432 law trace summary origin
  obtain ⟨requested,sibAt,outAt,nameAt,targetAt⟩ :=
    original_sibling_named_output_uses_parent_target432 parent.frame declared clauseAt writtenAt namedOutput
  let sibling : Request := ⟨q.occurrence ++ [siblingOrdinal],(parent.frame.whereFor clause).demand⟩
  have atSibling : parent.kids[siblingOrdinal]? = some sibling := sibAt
  obtain ⟨st,sd,se,sSrc,sPos,sDict,sSummary⟩ :=
    selected_parent_uses_actual_child_trace432 trace summary atSibling
  let ix : Fin sibling.demand.outputs.length :=
    ⟨siblingOutputOrdinal,(List.getElem?_eq_some_iff.mp outAt).1⟩
  have exactOutput : sibling.demand.outputs[ix] = requested :=
    (List.getElem?_eq_some_iff.mp outAt).2
  have exactTarget : sibling.demand.outputs[ix].target = origin.output.target := by
    rw [exactOutput,targetAt,original_binder_reserves_the_named_shared_target432 origin declared]
  have distinctSites : sibling.occurrence ≠ origin.child.occurrence := by
    intro h
    have slots : q.occurrence ++ [siblingOrdinal] = q.occurrence ++ [origin.clauseOrdinal] := h
    exact separate (by simpa using slots)
  refine ⟨pt,st,pd,sd,pe,pSrc,sibling,se,sSrc,ix,pPos,sPos,pDict,sDict,rfl,distinctSites,
    rfl,by rw [exactOutput,nameAt],exactTarget,?_⟩
  intro m fit
  obtain ⟨producer,_,u,pReceipt,first⟩ := pFacts m fit
  have retained : FixedTargets m se := by
    cases sSrc with
    | selected _ _ chosen _ _ => exact (law chosen m fit).2
  obtain ⟨v,sReceipt,second⟩ := retained ix
  rw [exactTarget] at sReceipt second
  exact ⟨producer,actual_named_trace_same_model_dictionary428 law sSrc m fit sd sSummary,
    u,v,pReceipt,sReceipt,⟨subtype_trans first.2 second.1,subtype_trans second.2 first.1⟩⟩

/-- Independent positive local rule to study two actual where siblings
in C16, not registered by R16. This is an authored singleton-parent
selection with exactly two original clauses sharing an output-only
binder and an invariant unary nominal RHS. A recursion, witness or
fit is not needed for local provenance; finite actual where traces
are still required to conclude any selected dictionary. -/
structure OriginalTwoNamedWhere433 {s : I72.State} {q : Request} (e : Event s q) where
  checked : Checked (authoredRegistry s.core.current)
  visibleOnly : visible s.core q = [e.frame.decl]
  rootSafe : ¬ RootCycle s q
  binder : OutputBinder
  declared : binder ∈ e.frame.decl.outputBinders
  body : Equation
  origin : OriginalWhereBinder395 e.frame binder body
  sibling : Clause
  exactlyTwo : e.frame.decl.requirements = [origin.entry.clause,sibling]
  inOrder : origin.clauseOrdinal = 0
  headName : Nat
  ctor : Nat
  syntaxHead : e.frame.decl.head = [.app ctor [.var headName]]
  producerInput : origin.entry.clause.arguments = [.var headName]
  siblingInput : sibling.arguments = [.var headName]
  siblingOutput : Equation
  siblingOutputAt : sibling.outputs = [siblingOutput]
  siblingValue : siblingOutput.rhs = .var binder.name
  out : Fin q.demand.outputs.length
  bodyAt : (e.outputs out).body = .explicit body
  normalized : GeneralDeclarationPatterns.normalize
    (GeneralDeclarativeOutputs320.bodyPattern (e.outputs out).body) = .app ctor [.var binder.name]
  parameter : Parameter
  use : Use s.core.current.environment ctor 1
  authoredModes : GeneralDeclarativeWitnessSparseIntervals357.names use.mode 1 = some [parameter]
  matchingTable : s.core.modes[ctor]? = some [parameter]
  valueKind : parameter.kind = .value
  invariant : (effectiveParameter false parameter).variance = .invariant
  literalTyped : HEq (e.outputs out).plan
    (invariantUnaryValuePlan432 ctor binder.name parameter use authoredModes matchingTable valueKind invariant)
  retained : RetainedTypedValueRows403 e

def twoNamedWhereParentRule433 : SourcePrimitives where
  elected _ _ e needs := needs = [] ∧ Nonempty (OriginalTwoNamedWhere433 e)
  other _ _ _ _ := False

theorem original_two_named_where_parent_local_law433 : SelectedLaw428 twoNamedWhereParentRule433 := by
  intro s q e needs picked m fit
  obtain ⟨source⟩ := picked.2
  exact ⟨⟨source_head_sound e.head m fit,
    fun i => original_named_mixed_output_meaning401 m (e.outputs i) source.checked⟩,
    retained_typed_rows_satisfy_fixed_targets403 source.retained m fit⟩

theorem sibling_literal_position_and_exact_value433
    {R : SourcePrimitives} (law : SelectedLaw428 R)
    {s : I72.State} {q : Request} {t : Tree} {e : Event s q}
    (trace : SourceTrace R s q t (some e))
    {key : Nat} {ds : List Dictionary} (sum : Summarizes t (.selected (.node key ds)))
    (source : OriginalTwoNamedWhere433 e) :
    ∃ (sib : Request) (se : Event s sib) (st : Tree)
      (sTr : SourceTrace R s sib st (some se)) (i : Fin sib.demand.outputs.length),
      ActualWhereTraceAt432 trace 1 sTr ∧
      sib.occurrence = q.occurrence ++ [1] ∧
      sib.demand.outputs[i].target = source.origin.output.target ∧
      ∀ m : I72.Model, Fits s m →
        ∃ v : Ty, (se.outputs i).receipt.actualEquation m =
          some (source.origin.output.target,v) ∧ Equivalent (m.assignment source.origin.output.target).1 v := by
  have two : (e.frame.decl.requirements)[1]? = some source.sibling := by
    rw [source.exactlyTwo]
    rfl
  have out : source.sibling.outputs[0]? = some source.siblingOutput := by
    rw [source.siblingOutputAt]
    rfl
  have other : 1 ≠ source.origin.clauseOrdinal := by simp [source.inOrder]
  obtain ⟨_,st,_,_,_,_,sib,se,sTr,i,_,position,_,_,site,_,_,_,target,_⟩ :=
    selected_named_sibling_replays_same_fixed_target433 law trace sum source.origin source.declared
      other two out source.siblingValue
  refine ⟨sib,se,st,sTr,i,position,site,target,?_⟩
  intro m fit
  have fixed : FixedTargets m se := by
    cases sTr with
    | selected _ _ picked _ _ => exact (law picked m fit).2
  obtain ⟨v,row,agree⟩ := fixed i
  rw [target] at row agree
  exact ⟨v,row,agree⟩

end Yulang.GeneralDeclarativeI65.I72.WhereAssociated432
