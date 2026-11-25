import Yulang.GeneralDeclarativeI65I72CompletedUnaryNextOutput406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (Tree Dictionary Result Summarizes)

/-- Factored front of the same unary rule. Literal inspection is
separate from the supplied post-selection original name. Replacing
the proof of completion does not replace the original request. -/
structure UnaryHeadAt406 (s : State) (q : Request) (row : Declaration) (need : OutputNeed s) where
  gate : CompletedUnaryGate406 s q row need
  rawSafe : ¬ RootCycle s q
  ordinal : Nat
  atOrdinal : unfilterOrdinal395 (fun d : Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 = some ordinal
  authored : (authoredRegistry s.core.current).declarations[ordinal]? = some row

def PreselectedUnary406.front {s q row needs forest}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest) :
    UnaryHeadAt406 s q row chosen.need :=
  ⟨chosen.gate,chosen.rootSafe,chosen.authoredOrdinal,chosen.exactOrdinal,chosen.declarationAt⟩

structure OriginalPathAt406 {s q row need} (front : UnaryHeadAt406 s q row need) where
  original : Origin
  inSource : original ∈ s.core.origins
  routed : OriginRoute s.core original front.gate.arg.center
  name : Nat
  decoded : literalUnaryPayloadName406 front.gate.key original.endpoint = some name
  fitsBounds : Bounds s.core.current.ordinary ⟨front.gate.lowerPayload,name,front.gate.upperPayload⟩

def OriginalPayload406.pathAt {s q row needs forest}
    {chosen : PreselectedUnary406 s q row (needs := needs) forest} (read : OriginalPayload406 chosen) :
    OriginalPathAt406 chosen.front :=
  ⟨read.source,read.authored,read.originalRoute,read.center,read.exactPath,read.retainedBounds⟩

def unaryFrameAt406 {s q row need}
    (front : UnaryHeadAt406 s q row need) (read : OriginalPathAt406 front) :
    AuthoredBodyFrame393 s.core q :=
  frameAtSource395 (by simp [front.gate.only]) front.ordinal front.authored unusedPlacement403
    (fun n => if n = front.gate.binder
      then ⟨front.gate.lowerPayload,read.name,front.gate.upperPayload⟩ else emptyCapture403)

def UnaryHeadAt406.visits {s q row need} (head : UnaryHeadAt406 s q row need) : List CandidateVisit :=
  [⟨head.ordinal,0,[],.value,false,head.gate.arg.lower⟩]

theorem no_unsafe_step_in_that_native_root406 {s q row need}
    (head : UnaryHeadAt406 s q row need) :
    ∀ step ∈ head.visits, step.declarationOrdinal = head.ordinal ∧ ¬CurrentCycleAt s step.site := by
  intro step seen
  cases List.mem_singleton.mp seen
  exact ⟨rfl,fun cyclic => head.rawSafe ⟨head.gate.arg,by simp [head.gate.exactArg],cyclic⟩⟩

/-- The producer may be a previously established C406 native event,
rather than something representable by the old authored head type. -/
structure FiniteUnaryStep406 (s : State) (q : Request) (need : OutputNeed s) (trees : List Tree) where
  row : Declaration
  head : UnaryHeadAt406 s q row need
  actual : OriginalPathAt406 head
  output : ∀ i : Fin q.demand.outputs.length, NamedMixedOutput401 s.b6 (unaryFrameAt406 head actual) i
  fixed : ∀ i : Fin q.demand.outputs.length, ∃ rhs : Expr,
    fixedValueCode403 (output i).rhs = some rhs ∧
      (⟨q.demand.outputs[i].target,rhs⟩ : Equation) ∈ s.core.current.ordinary.equations
  clauses : LiteralVariableWhere403 row
  kids : WhereForest PriorSource406 s (frameWhereKids400 (unaryFrameAt406 head actual)) trees

def CompletedInvocation406.liftStep {s q trees} (invoke : CompletedInvocation406 s q trees) :
    FiniteUnaryStep406 s q invoke.chosen.need trees :=
  ⟨invoke.row,invoke.chosen.front,invoke.actualPayload.pathAt,invoke.body.output,invoke.fixed,
    invoke.clauses,invoke.children⟩

/-- Finite, literally selected producers with indexed original
receipts. A diagnostic by itself does not create a constructor; the
same source's proof reads each original output ordinal. In the new
case the exact named read at the previous ordinal is part of the
next Head's type. The where forest is still the verified prior one. -/
inductive FiniteNative406 (s : State) :
    (q : Request) → Dictionary → (Fin q.demand.outputs.length → NamedMixedReceipt401 s.core) → Type where
  | base {q : Request} {t : Tree} {d : Dictionary}
      {original : Fin q.demand.outputs.length → NamedMixedReceipt401 s.core}
      (source : ScopedSource406 s q t) (done : Summarizes t (.selected d))
      (every : ∀ i : Fin q.demand.outputs.length, ScopedOutputRead406 s q source i (original i)) :
      FiniteNative406 s q d original
  | advance {p : Request} {d : Dictionary}
      {original : Fin p.demand.outputs.length → NamedMixedReceipt401 s.core}
      (producer : FiniteNative406 s p d original)
      {i : Fin p.demand.outputs.length} {dChildren : List Dictionary}
      (step : FiniteUnaryStep406 s q ⟨p,d,i,original i⟩ trees)
      (whereDone : CommonRoleOutermostResolver.All₂ Summarizes trees (dChildren.map Result.selected)) :
      FiniteNative406 s q (.node step.row.id dChildren) (fun j => (step.output j).receipt)

theorem any_actual_scoped_selection_is_a_finite_base406 {s q t d}
    (source : ScopedSource406 s q t) (done : Summarizes t (.selected d)) :
    ∃ outputs, Nonempty (FiniteNative406 s q d outputs) := by
  classical
  have each : ∀ i : Fin q.demand.outputs.length, ∃ r, Nonempty (ScopedOutputRead406 s q source i r) :=
    read_exact_output_of_actual_selected_trace406 source done
  let original (i : Fin q.demand.outputs.length) := Classical.choose (each i)
  let atSource (i : Fin q.demand.outputs.length) : ScopedOutputRead406 s q source i (original i) :=
    Classical.choice (Classical.choose_spec (each i))
  exact ⟨original,⟨.base source done atSource⟩⟩

theorem finite_native_producer_preserves_the_original_output_address406 {s q d original}
    (trace : FiniteNative406 s q d original) (i : Fin q.demand.outputs.length) :
    (original i).occurrence = q.occurrence ∧ (original i).outputOrdinal = i.val ∧
      (original i).original = q.demand.outputs[i] := by
  cases trace with
  | base _ _ each => exact exact_scoped_receipt_keeps_its_request_and_ordinal406 (each i)
  | advance => exact ⟨rfl,rfl,rfl⟩

theorem chosen_finite_native_output_retains_exact_nominal406 {s q d original}
    (trace : FiniteNative406 s q d original) (i : Fin q.demand.outputs.length)
    {a : Capture} {key : Nat} {args : List Expr}
    (target : (original i).original.target = a.lower)
    (declared : DeclaredHead404 key (original i).rhs)
    (code : fixedValueCode403 (original i).rhs = some (.nominal key args)) :
    (⟨a.lower,.nominal key args⟩ : Equation) ∈ s.core.current.ordinary.equations := by
  cases trace with
  | base source done every =>
    exact even_new_completed_trace_protects_an_original_nominal_output406 done (every i) target declared code
  | advance earlier step whereDone =>
    obtain ⟨old,encoded,retained⟩ := step.fixed i
    have same : old = .nominal key args := Option.some.inj (encoded.symm.trans code)
    have fixedTarget : q.demand.outputs[i].target = a.lower := target
    simpa only [same,fixedTarget] using retained

theorem raw_K2_still_precedes_finite_native_rule406 {s q d original}
    (raw : RootCycle s q) (trace : FiniteNative406 s q d original) : False := by
  cases trace with
  | base source done every =>
    have rejected := raw_k2_forces_new_trace_verdict406 raw source
    rw [rejected] at done
    cases done
  | advance earlier step whereDone => exact step.head.rawSafe raw

end Yulang.GeneralDeclarativeI65.I72
