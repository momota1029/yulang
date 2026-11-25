import Yulang.GeneralDeclarativeI65I72OrderedNativeElection407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeDemand320 (Bounds bounds_sound)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonNominalFullCarrier (Equivalent)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open CommonRoleOutermostResolver (Tree Dictionary Summarizes Result All₂)

def ElectedNativeHead407.row {s q need input}
    (e : ElectedNativeHead407 (s := s) (q := q) (need := need) input) : Declaration :=
  (visible s.core q)[e.winner]

def ElectedNativeHead407.source {s q need input}
    (e : ElectedNativeHead407 (s := s) (q := q) (need := need) input) :
    VisibleRoot407 s q e.winner :=
  input.roots e.winner

structure NativeActualPath407 {s q need} (input : NativeElectionInput407 s q need) where
  original : Origin
  inSource : original ∈ s.core.origins
  route : OriginRoute s.core original input.read.arg.center
  name : Nat
  decoded : literalUnaryPayloadName406 input.read.found original.endpoint = some name
  bounds : Bounds s.core.current.ordinary ⟨input.read.sourcePayload,name,input.positive.upperPayload⟩

def OrderedNativeFrame407 {s q need input}
    (e : ElectedNativeHead407 (s := s) (q := q) (need := need) input)
    (actual : NativeActualPath407 input) : AuthoredBodyFrame393 s.core q :=
  frameAtSource395 (List.getElem_mem e.winner.isLt) e.source.sourceOrdinal e.source.declarationAt unusedPlacement403
    (fun n => if n = e.source.unary.binder
      then ⟨input.read.sourcePayload,actual.name,input.positive.upperPayload⟩ else emptyCapture403)

structure OrderedNativeStep407 {s q need} (input : NativeElectionInput407 s q need) (trees : List Tree) where
  elected : ElectedNativeHead407 input
  actual : NativeActualPath407 input
  output : ∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 s.b6 (OrderedNativeFrame407 elected actual) i
  fixed : ∀ i : Fin q.demand.outputs.length, ∃ rhs : Expr,
    fixedValueCode403 (output i).rhs = some rhs ∧
      (⟨q.demand.outputs[i].target,rhs⟩ : Equation) ∈ s.core.current.ordinary.equations
  clauses : LiteralVariableWhere403 elected.row
  kids : WhereForest PriorSource406 s (frameWhereKids400 (OrderedNativeFrame407 elected actual)) trees

def OrderedNativeStep407.frame {s q need input trees}
    (step : OrderedNativeStep407 (s := s) (q := q) (need := need) input trees) : AuthoredBodyFrame393 s.core q :=
  OrderedNativeFrame407 step.elected step.actual

def OrderedNativeStep407.written {s q need input trees}
    (step : OrderedNativeStep407 (s := s) (q := q) (need := need) input trees) :
    List (NamedMixedReceipt401 s.core) :=
  List.ofFn fun i => (step.output i).receipt

structure OrderedNativeMeaning407 {s q need input trees}
    (step : OrderedNativeStep407 (s := s) (q := q) (need := need) input trees) (m : Model) : Prop where
  lower : Equivalent (m.assignment input.read.arg.lower).1
    (value (environment m.assignment) .actual (.nominal input.read.found [.variable input.read.sourcePayload]))
  upper : m.nativeSyntax input.positive.upper.slot =
    some (unaryNominalPoint404 input.read.found input.positive.upperPayload)
  lowerWell : ContextWellFormed s.core.modes false (unaryNominalPoint404 input.read.found input.read.sourcePayload)
  upperWell : ContextWellFormed s.core.modes false (unaryNominalPoint404 input.read.found input.positive.upperPayload)
  comparison : ContextDerives s.core.modes m.assignment false
    (unaryNominalPoint404 input.read.found input.read.sourcePayload)
    (unaryNominalPoint404 input.read.found input.positive.upperPayload)
  sameActual : m.nativeSyntax step.actual.original.slot =
    some (unaryNominalPoint404 input.read.found (step.frame.input step.elected.source.unary.binder).center)
  bounds : InInterval (m.assignment input.read.sourcePayload).1 (m.assignment input.positive.upperPayload).1
    (m.assignment (step.frame.input step.elected.source.unary.binder).center).1
  outputs : ∀ i : Fin q.demand.outputs.length, ExactNamedOutputMeaning401 m (step.output i) ∧
    ∃ v, (step.output i).receipt.actualEquation m = some (q.demand.outputs[i].target,v) ∧
      Equivalent (m.assignment q.demand.outputs[i].target).1 v

theorem native_mixed_tag_step_uses_same_model_and_exact_output407 {s p d original q trees}
    (before : FiniteNative406 s p d original) (i : Fin p.demand.outputs.length)
    {input : NativeElectionInput407 s q ⟨p,d,i,original i⟩}
    (step : OrderedNativeStep407 input trees) (m : Model) (fit : Fits s m) :
    OrderedNativeMeaning407 step m := by
  have retained := (completed_read_is_literal_and_retained407 before i input.read).1
  obtain ⟨compare⟩ := actual_native_upper_derives_comparison407 input.read input.positive
  obtain ⟨lo,hi,related⟩ := in_same_model compare m.assignment fit.1.1
  have actualName : (step.frame.input step.elected.source.unary.binder).center = step.actual.name := by
    change (if step.elected.source.unary.binder = step.elected.source.unary.binder
      then (⟨input.read.sourcePayload,step.actual.name,input.positive.upperPayload⟩ : Capture)
      else emptyCapture403).center = _
    simp
  refine ⟨fit.1.1.2 _ retained,?_,lo,hi,related,?_,?_,?_⟩
  · rw [← input.positive.upperLiteral]
    exact fit.2 _ input.positive.upperAuthored
  · rw [actualName,← unary_payload_name_read_exact406.mp step.actual.decoded]
    exact fit.2 _ step.actual.inSource
  · rw [actualName]
    exact bounds_sound step.actual.bounds m.assignment fit.1.1
  · intro j
    refine ⟨original_named_mixed_output_meaning401 m (step.output j) input.checked,?_⟩
    obtain ⟨code,printed,row⟩ := step.fixed j
    have denotation := fixed_value_code_same_model403 (step.output j).rhs m code printed
    refine ⟨value (environment m.assignment) .actual code,?_, fit.1.1.2 _ row⟩
    simp only [NamedMixedReceipt401.actualEquation,NamedMixedOutput401.receipt,denotation,Option.map_some]

structure OrderedNativeLedger407 {s p d original q trees}
    {before : FiniteNative406 s p d original} {i : Fin p.demand.outputs.length}
    {input : NativeElectionInput407 s q ⟨p,d,i,original i⟩}
    (step : OrderedNativeStep407 input trees) (dKids : List Dictionary) where
  lower : FiniteNativeLedger406 s before
  whereTree : I72.GeneralForest step.kids dKids

def OrderedNativeLedger407.written {s p d original q trees before i input step dKids}
    (ledger : OrderedNativeLedger407 (s := s) (p := p) (d := d) (original := original) (q := q)
      (trees := trees) (before := before) (i := i) (input := input) step dKids) :
      List (NamedMixedReceipt401 s.core) :=
  step.written ++ ledger.whereTree.ledger.written

theorem actual_ordered_native_selection_assembles_one_ledger407 {s p d original q trees dKids}
    (before : FiniteNative406 s p d original) (i : Fin p.demand.outputs.length)
    {input : NativeElectionInput407 s q ⟨p,d,i,original i⟩}
    (step : OrderedNativeStep407 input trees)
    (done : All₂ Summarizes trees (dKids.map Result.selected)) :
    ∃ ledger : OrderedNativeLedger407 (before := before) step dKids,
      (∀ visit ∈ CompletedVisits407 input.read input.roots, ¬CurrentCycleAt s visit.site) ∧
      CompleteScopeWhere405 step.kids ∧
      ∀ m, Fits s m → OrderedNativeMeaning407 step m ∧ ledger.lower.Means m ∧
        DictionaryEvidenceForest s m (frameWhereKids400 step.frame) dKids := by
  obtain ⟨_,earlier,meaning⟩ := finite_completed_native_source_assembles_exact_ledger406 before
  obtain ⟨⟨whereTree⟩,_⟩ := (lower_selected_at_exact_trace _
    s (authored_native_source_provides_nodes405 s)).forest step.kids done
  exact ⟨⟨earlier,whereTree⟩,
    ordered_completed_visits_use_only_raw_root407 input.read input.roots input.rawSafe,
    actual_prior_where_keeps_grounded_priority406 step.kids,fun m fit =>
      ⟨native_mixed_tag_step_uses_same_model_and_exact_output407 before i step m fit,
        meaning m fit, prior_where_dictionary_uses_one_model406 whereTree m fit⟩⟩

end Yulang.GeneralDeclarativeI65.I72
