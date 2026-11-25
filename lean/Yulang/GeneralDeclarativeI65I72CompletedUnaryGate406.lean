import Yulang.GeneralDeclarativeI65I72CanonicalMixedPriority405

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (Legal names visited visitedList)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open CommonNominalFullCarrier (Equivalent)
open PresenceNormalForm (Atom)

abbrev PriorSource406 := authoredNativeSelectedSource405

/-- A literal unary candidate tested at its original, sole demand
position. Its lower source is the original complete output, never
an authored Origin. Upper syntax is independently authored. The
written child is a variable, so no constructor child is inspected. -/
structure CompletedUnaryGate406 (s : State) (q : Request) (row : Declaration)
    (need : OutputNeed s) where
  key : Nat
  binder : Nat
  arg : Capture
  exactArg : q.demand.arguments = [arg]
  exactHead : row.head = [authoredUnaryPattern405 key binder]
  only : visible s.core q = [row]
  checked : Checked (authoredRegistry s.core.current)
  covered : DeclarationCovered s.core.current.environment row
  lowerPayload : Nat
  lowerTarget : need.expected.original.target = arg.lower
  lowerTyped : TypedCovariantPoint404 key lowerPayload need.expected.rhs
  upper : Origin
  upperAuthored : upper ∈ s.core.origins
  upperRoute : OriginRoute s.core upper arg.upper
  upperPayload : Nat
  upperLiteral : upper.endpoint = unaryNominalPoint404 key upperPayload
  compared : Atom.tyLe (.var lowerPayload) (.var upperPayload) ∈ s.core.current.ordinary.normal.ordinary

def CompletedUnaryGate406.required {s q row need} (gate : CompletedUnaryGate406 s q row need) :
    LiteralInputNeed404 s gate.arg need :=
  let exacts := actual_typed_point_yields_literal_declared_code404 need.expected.rhs gate.lowerTyped
  ⟨gate.key,[.variable gate.lowerPayload],gate.lowerTarget,exacts.1,exacts.2⟩

private theorem covariant_point_wellformed406 {s : State} {key arg : Nat}
    (table : s.core.modes[key]? = some [coValue404]) :
    ContextWellFormed s.core.modes false (unaryNominalPoint404 key arg) :=
  .nominal table (.cons (.valuePoint (.ordinary false (.var arg))) (.nil false))

theorem literal_input_declares_mode_and_compares406 {s q row need}
    (gate : CompletedUnaryGate406 s q row need) :
    Nonempty (DeclaredComparison s.core.current.environment s.core.current.ordinary s.core.modes
      false (unaryNominalPoint404 gate.key gate.lowerPayload)
        (unaryNominalPoint404 gate.key gate.upperPayload)) := by
  obtain ⟨use,mode,table⟩ := original_typed_point_has_canonical_declared_mode404 need.expected.rhs gate.lowerTyped
  have authority : Legal s.core.current.environment s.core.modes (gate.key,1) := by
    refine ⟨use,[coValue404],?_,table⟩
    change names use.mode 1 = some [coValue404]
    rw [mode]; rfl
  refine ⟨⟨?_,covariant_point_wellformed406 table,covariant_point_wellformed406 table,
    .nominal table (.cons (.covariantValue (.ordinary gate.compared)) .nil)⟩⟩
  intro candidate visitedAt
  have index : candidate = (gate.key,1) := by
    simpa [unaryNominalPoint404,visited,visitedList] using visitedAt
  exact index ▸ authority

/-- Selection prior to body readback. It stores the already selected
finite producer, the original written head and addresses, and
independently checked endpoint comparison. There is no observation
of an actual-center row, no model and no physical grant. -/
structure PreselectedUnary406 (s : State) (q : Request) (row : Declaration)
    {needs : List (OutputNeed s)} (forest : SupportForest PriorSource406 s needs) where
  need : OutputNeed s
  needOrdinal : Nat
  exactNeed : needs[needOrdinal]? = some need
  gate : CompletedUnaryGate406 s q row need
  rootSafe : ¬RootCycle s q
  authoredOrdinal : Nat
  exactOrdinal : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 = some authoredOrdinal
  declarationAt : (authoredRegistry s.core.current).declarations[authoredOrdinal]? = some row

def PreselectedUnary406.producer {s q row needs forest}
    (winner : PreselectedUnary406 s q row (needs := needs) forest) :
    ExactOutputSupport PriorSource406 s winner.need :=
  forest.atOriginal winner.needOrdinal winner.exactNeed

def PreselectedUnary406.visits {s q row needs forest}
    (win : PreselectedUnary406 s q row (needs := needs) forest) : List CandidateVisit :=
  [⟨win.authoredOrdinal,0,[],.value,false,win.gate.arg.lower⟩]

theorem actual_completed_lower_selects_before_original_center406 {s q row needs need}
    (gate : CompletedUnaryGate406 s q row need)
    (forest : SupportForest PriorSource406 s needs) (n : Nat) (atN : needs[n]? = some need)
    (safe : ¬RootCycle s q) :
    Nonempty (PreselectedUnary406 s q row forest) := by
  have order : (visible s.core q)[0]? = some row := by simp [gate.only]
  obtain ⟨i,atI,actual⟩ := unfilterOrdinal395_exact
    (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 order
  exact ⟨⟨need,n,atN,gate,safe,i,atI,actual⟩⟩

theorem completed_root_never_inspects_variable_payload406 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) :
    (∀ v ∈ chosen.visits, v.declarationOrdinal = chosen.authoredOrdinal ∧ ¬CurrentCycleAt s v.site) ∧
    (∀ view site dst, ¬GeneralDeclarativeInspect321.Visit view site (.variable chosen.gate.binder) dst) := by
  refine ⟨?_,fun _ _ _ => GeneralDeclarativeInspect321.variable_has_no_visit⟩
  intro v entered
  have same := List.mem_singleton.mp entered
  subst v
  exact ⟨rfl,fun hit => chosen.rootSafe ⟨chosen.gate.arg,by simp [chosen.gate.exactArg],hit⟩⟩

/-- One interpretation, but two distinct sources: lower is licensed
by the original retained B6 term and raw ordinary assignment; upper
is the actual authored endpoint syntax. Never infer nativeSyntax
for the completed lower from its ordinary value. -/
theorem completed_selected_endpoints_have_same_model406 {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest)
    (m : Model) (fit : Fits s m) :
    (⟨chosen.gate.arg.lower,.nominal chosen.gate.key [.variable chosen.gate.lowerPayload]⟩ : Equation)
      ∈ s.core.current.ordinary.equations ∧
    Equivalent (m.assignment chosen.gate.arg.lower).1
      (value (environment m.assignment) .actual (.nominal chosen.gate.key [.variable chosen.gate.lowerPayload])) ∧
    m.nativeSyntax chosen.gate.upper.slot = some (unaryNominalPoint404 chosen.gate.key chosen.gate.upperPayload) ∧
    ContextWellFormed s.core.modes false (unaryNominalPoint404 chosen.gate.key chosen.gate.lowerPayload) ∧
    ContextWellFormed s.core.modes false (unaryNominalPoint404 chosen.gate.key chosen.gate.upperPayload) ∧
      ContextDerives s.core.modes m.assignment false (unaryNominalPoint404 chosen.gate.key chosen.gate.lowerPayload)
        (unaryNominalPoint404 chosen.gate.key chosen.gate.upperPayload) := by
  obtain ⟨compared⟩ := literal_input_declares_mode_and_compares406 chosen.gate
  have retained := completed_input_owns_retained_nominal404 authored_native_source_keeps_own_fixed_rows405
    chosen.gate.required chosen.producer
  refine ⟨retained,fit.1.1.2 _ retained,?_,in_same_model compared m.assignment fit.1.1⟩
  rw [← chosen.gate.upperLiteral]
  exact fit.2 _ chosen.gate.upperAuthored

end Yulang.GeneralDeclarativeI65.I72
