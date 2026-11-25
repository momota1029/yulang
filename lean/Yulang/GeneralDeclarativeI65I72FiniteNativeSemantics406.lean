import Yulang.GeneralDeclarativeI65I72FiniteNativeInputs406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Tree Dictionary Summarizes Result All₂)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeDemand320 (bounds_sound)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier (Equivalent)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)

def FiniteUnaryStep406.frame {s q need trees} (step : FiniteUnaryStep406 s q need trees) :
    AuthoredBodyFrame393 s.core q := unaryFrameAt406 step.head step.actual

def FiniteUnaryStep406.written {s q need trees} (step : FiniteUnaryStep406 s q need trees) :
    List (NamedMixedReceipt401 s.core) :=
  List.ofFn fun i => (step.output i).receipt

structure FiniteStepMeaning406 {s q need trees} (step : FiniteUnaryStep406 s q need trees) (m : Model) : Prop where
  lower : Equivalent (m.assignment step.head.gate.arg.lower).1
    (value (environment m.assignment) .actual (.nominal step.head.gate.key [.variable step.head.gate.lowerPayload]))
  authoredUpper : m.nativeSyntax step.head.gate.upper.slot =
    some (unaryNominalPoint404 step.head.gate.key step.head.gate.upperPayload)
  lowerWellFormed : ContextWellFormed s.core.modes false
    (unaryNominalPoint404 step.head.gate.key step.head.gate.lowerPayload)
  upperWellFormed : ContextWellFormed s.core.modes false
    (unaryNominalPoint404 step.head.gate.key step.head.gate.upperPayload)
  typed : ContextDerives s.core.modes m.assignment false
    (unaryNominalPoint404 step.head.gate.key step.head.gate.lowerPayload)
    (unaryNominalPoint404 step.head.gate.key step.head.gate.upperPayload)
  actualPayload : m.nativeSyntax step.actual.original.slot = some
    (unaryNominalPoint404 step.head.gate.key (step.frame.input step.head.gate.binder).center)
  bound : InInterval (m.assignment step.head.gate.lowerPayload).1 (m.assignment step.head.gate.upperPayload).1
    (m.assignment (step.frame.input step.head.gate.binder).center).1
  outputs : ∀ i : Fin q.demand.outputs.length, ExactNamedOutputMeaning401 m (step.output i) ∧
    ∃ v, (step.output i).receipt.actualEquation m = some (q.demand.outputs[i].target,v) ∧
      Equivalent (m.assignment q.demand.outputs[i].target).1 v

theorem finite_step_uses_only_exact_predecessor_output406 {s p d original q trees}
    (before : FiniteNative406 s p d original) (i : Fin p.demand.outputs.length)
    (step : FiniteUnaryStep406 s q ⟨p,d,i,original i⟩ trees) (m : Model) (fit : Fits s m) :
    FiniteStepMeaning406 step m := by
  have source := actual_typed_point_yields_literal_declared_code404 (original i).rhs step.head.gate.lowerTyped
  have retained := chosen_finite_native_output_retains_exact_nominal406 before i
    step.head.gate.lowerTarget source.1 source.2
  obtain ⟨compare⟩ := literal_input_declares_mode_and_compares406 step.head.gate
  obtain ⟨lo,hi,related⟩ := in_same_model compare m.assignment fit.1.1
  have actualName : (step.frame.input step.head.gate.binder).center = step.actual.name := by
    change (if step.head.gate.binder = step.head.gate.binder
      then (⟨step.head.gate.lowerPayload,step.actual.name,step.head.gate.upperPayload⟩ : GeneralDeclarativeWhere319.Capture)
      else emptyCapture403).center = _
    simp
  refine ⟨fit.1.1.2 _ retained,?_,lo,hi,related,?_,?_,?_⟩
  · rw [← step.head.gate.upperLiteral]
    exact fit.2 _ step.head.gate.upperAuthored
  · rw [actualName,← unary_payload_name_read_exact406.mp step.actual.decoded]
    exact fit.2 _ step.actual.inSource
  · rw [actualName]
    exact bounds_sound step.actual.fitsBounds m.assignment fit.1.1
  · intro i
    refine ⟨original_named_mixed_output_meaning401 m (step.output i) step.head.gate.checked,?_⟩
    obtain ⟨code,printed,row⟩ := step.fixed i
    have denotation := fixed_value_code_same_model403 (step.output i).rhs m code printed
    refine ⟨value (environment m.assignment) .actual code,?_, fit.1.1.2 _ row⟩
    simp only [NamedMixedReceipt401.actualEquation,NamedMixedOutput401.receipt,denotation,Option.map_some]

/-- Indexed by the precise finite selected proof. At each new step
the producer's grounded ledger is a dependency, not added to the
consumer's written or where receipts. -/
inductive FiniteNativeLedger406 (s : State) :
    {q : Request} → {d : Dictionary} → {original : Fin q.demand.outputs.length → NamedMixedReceipt401 s.core} →
    FiniteNative406 s q d original → Type where
  | base {source : ScopedSource406 s q t} {done : Summarizes t (.selected d)}
      {original : Fin q.demand.outputs.length → NamedMixedReceipt401 s.core}
      {reads : ∀ i : Fin q.demand.outputs.length, ScopedOutputRead406 s q source i (original i)}
      (ledger : ScopedLedger406 s q d) (aligned : GroundedReplayOn406 source ledger) :
      FiniteNativeLedger406 s (.base source done reads)
  | advance {p : Request} {d : Dictionary} {original : Fin p.demand.outputs.length → NamedMixedReceipt401 s.core}
      {before : FiniteNative406 s p d original} {i : Fin p.demand.outputs.length}
      {step : FiniteUnaryStep406 s q ⟨p,d,i,original i⟩ trees}
      {whereDone : All₂ Summarizes trees (childrenD.map Result.selected)}
      (lower : FiniteNativeLedger406 s before) (whereTree : I72.GeneralForest step.kids childrenD) :
      FiniteNativeLedger406 s (.advance before step whereDone)

def FiniteNativeLedger406.written {s q d original} {trace : FiniteNative406 s q d original}
    (ledger : FiniteNativeLedger406 s trace) : List (NamedMixedReceipt401 s.core) :=
  match ledger with
  | .base earlier _ => earlier.written
  | @FiniteNativeLedger406.advance _ _ _ _ _ _ _ _ _ step _ _ later => step.written ++ later.ledger.written

def FiniteNativeLedger406.Means {s q d original} {trace : FiniteNative406 s q d original}
    (ledger : FiniteNativeLedger406 s trace) (m : Model) : Prop :=
  match ledger with
  | .base earlier _ => earlier.Means m ∧ ScopedEvidence406 s m q d
  | @FiniteNativeLedger406.advance _ _ _ childrenD _ _ _ _ _ step _ lower later =>
    FiniteStepMeaning406 step m ∧ lower.Means m ∧ DictionaryEvidenceForest s m
      (frameWhereKids400 step.frame) childrenD

/-- All original visited roots and recursive producer proofs in the
selected support chain are certified; where proof order is retained
separately. The same assembled ledger works in every fitting model. -/
def FiniteRootPriorities406 {s q d original} (trace : FiniteNative406 s q d original) : Prop :=
  match trace with
  | .base _ _ _ => True
  | .advance earlier step _ =>
    FiniteRootPriorities406 earlier ∧ CompleteScopeWhere405 step.kids ∧
      ∀ site ∈ step.head.visits, site.declarationOrdinal = step.frame.ordinal ∧ ¬CurrentCycleAt s site.site

theorem finite_completed_native_source_assembles_exact_ledger406 {s q d original}
    (trace : FiniteNative406 s q d original) :
    FiniteRootPriorities406 trace ∧
      ∃ ledger : FiniteNativeLedger406 s trace, ∀ m, Fits s m → ledger.Means m := by
  induction trace with
  | base source done reads =>
    obtain ⟨ledger,same,models⟩ := actual_scoped_trace_assembles_one_ledger406 source done
    exact ⟨True.intro,.base ledger same,models⟩
  | @advance q trees p d original earlier i children step whereDone ih =>
    obtain ⟨before,ledger,allModels⟩ := ih
    obtain ⟨⟨whereTree⟩,_⟩ := (lower_selected_at_exact_trace _ s
      (authored_native_source_provides_nodes405 s)).forest step.kids whereDone
    refine ⟨⟨before,actual_prior_where_keeps_grounded_priority406 step.kids,
      no_unsafe_step_in_that_native_root406 step.head⟩,
      .advance ledger whereTree,fun m fit => ?_⟩
    exact ⟨finite_step_uses_only_exact_predecessor_output406 earlier i step m fit,
      allModels m fit,prior_where_dictionary_uses_one_model406 whereTree m fit⟩

end Yulang.GeneralDeclarativeI65.I72
