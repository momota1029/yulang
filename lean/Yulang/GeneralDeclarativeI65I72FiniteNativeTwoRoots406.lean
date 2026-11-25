import Yulang.GeneralDeclarativeI65I72FiniteNativeSemantics406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Result Tree Dictionary Summarizes)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

def completed_native_root_as_real_producer406 {s q trees d} (first : CompletedInvocation406 s q trees)
    (done : Summarizes (.selected first.row.id trees) (.selected d)) :
    FiniteNative406 s q d (fun i => (first.body.output i).receipt) :=
  .base (.completed first) done (fun _ => .completed first)

/-- The next candidate is *constructed*, not assumed as a successful
head. In particular, the predecessor can be the newly scoped
completed-lower rule, which cannot be erased to an old authored
head merely to pass the interface. No output or invocation is
sought by equality of denotations. -/
theorem actual_new_native_root_feeds_another_exact_native_root406 {s p q row trees d}
    (first : CompletedInvocation406 s p trees)
    (done : Summarizes (.selected first.row.id trees) (.selected d))
    (i : Fin p.demand.outputs.length)
    (gate : CompletedUnaryGate406 s q row ⟨p,d,i,(first.body.output i).receipt⟩)
    (safe : ¬RootCycle s q)
    (source : Origin) (authored : source ∈ s.core.origins)
    (routed : OriginRoute s.core source gate.arg.center) {inputName : Nat}
    (decoded : literalUnaryPayloadName406 gate.key source.endpoint = some inputName)
    (constraints : Bounds s.core.current.ordinary ⟨gate.lowerPayload,inputName,gate.upperPayload⟩)
    (noWhere : row.requirements = []) (noOutputs : q.demand.outputs = []) :
    ∃ step : FiniteUnaryStep406 s q ⟨p,d,i,(first.body.output i).receipt⟩ [],
      step.row = row ∧ step.actual.name = inputName ∧
      (∀ site ∈ step.head.visits, site.declarationOrdinal = step.frame.ordinal ∧ ¬CurrentCycleAt s site.site) ∧
      ∃ ledger : FiniteNativeLedger406 s
          (FiniteNative406.advance (completed_native_root_as_real_producer406 first done) step
            (dChildren := []) .nil),
        ∀ m, Fits s m → ledger.Means m := by
  have lookup : (visible s.core q)[0]? = some row := by simp [gate.only]
  obtain ⟨j,exact,authoredRow⟩ := unfilterOrdinal395_exact
    (fun row : GeneralDeclarations.Declaration => row.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 lookup
  let front : UnaryHeadAt406 s q row ⟨p,d,i,(first.body.output i).receipt⟩ :=
    ⟨gate,safe,j,exact,authoredRow⟩
  let path : OriginalPathAt406 front := ⟨source,authored,routed,inputName,decoded,constraints⟩
  have noI : ∀ j : Fin q.demand.outputs.length, False := by
    intro j
    obtain ⟨n,impossible⟩ := j
    simp [noOutputs] at impossible
  have child : frameWhereKids400 (unaryFrameAt406 front path) = [] := by
    simp [frameWhereKids400,AuthoredBodyFrame393.clauses,unaryFrameAt406,frameAtSource395,noWhere,children]
  let step : FiniteUnaryStep406 s q ⟨p,d,i,(first.body.output i).receipt⟩ [] :=
    ⟨row,front,path,fun j => (noI j).elim,fun j => (noI j).elim,
      by simp [LiteralVariableWhere403,noWhere],child.symm ▸ .nil⟩
  exact ⟨step,rfl,rfl,no_unsafe_step_in_that_native_root406 step.head,
    (finite_completed_native_source_assembles_exact_ledger406
      (FiniteNative406.advance (completed_native_root_as_real_producer406 first done) step
        (dChildren := []) .nil)).2⟩

end Yulang.GeneralDeclarativeI65.I72
