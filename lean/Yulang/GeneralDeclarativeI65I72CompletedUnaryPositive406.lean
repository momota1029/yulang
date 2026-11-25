import Yulang.GeneralDeclarativeI65I72CompletedUnaryLedger406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Tree Result Dictionary Summarizes)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

def exactPriorComplete406 {s producer t e d}
    (trace : SourceTrace PriorSource406 s producer t (some e))
    (done : Summarizes t (.selected d)) (i : Fin producer.demand.outputs.length) :
    SupportForest PriorSource406 s [needOfSelected404 e d i] :=
  .cons trace done rfl .nil

noncomputable def preselectAtExactPriorComplete406 {s producer q row t e d}
    (trace : SourceTrace PriorSource406 s producer t (some e))
    (done : Summarizes t (.selected d)) (i : Fin producer.demand.outputs.length)
    (gate : CompletedUnaryGate406 s q row (needOfSelected404 e d i))
    (safe : ¬RootCycle s q) :
    PreselectedUnary406 s q row (exactPriorComplete406 trace done i) :=
  let original := unfilterOrdinal395_exact (fun d : GeneralDeclarations.Declaration => d.role == q.demand.role)
    (authoredRegistry s.core.current).declarations 0 (by
      change (visible s.core q)[0]? = some row
      simp [gate.only])
  ⟨needOfSelected404 e d i,0,rfl,gate,safe,Classical.choose original,
    (Classical.choose_spec original).1,(Classical.choose_spec original).2⟩

theorem original_prior_proof_is_the_literal_native_dependency406 {s producer q row t e d}
    (trace : SourceTrace PriorSource406 s producer t (some e))
    (done : Summarizes t (.selected d)) (i : Fin producer.demand.outputs.length)
    (gate : CompletedUnaryGate406 s q row (needOfSelected404 e d i)) (safe : ¬RootCycle s q) :
    let chosen := preselectAtExactPriorComplete406 trace done i gate safe
    chosen.producer.source = trace ∧ chosen.producer.event = e ∧
      chosen.producer.sameTypedOutput = (rfl : (e.outputs i).receipt = (e.outputs i).receipt) :=
  ⟨rfl,rfl,rfl⟩

/-- A direct successful selection, not a chosen consumer hypothesis.
The only input read after election is the original typed indication
at its consumer input path. The actual old selected trace is fed to
this root, and the new selected evidence really uses that same root. -/
theorem given_prior_selected_output_opens_completed_native406
    {s producer q row t e d}
    (trace : SourceTrace PriorSource406 s producer t (some e))
    (done : Summarizes t (.selected d)) (i : Fin producer.demand.outputs.length)
    (gate : CompletedUnaryGate406 s q row (needOfSelected404 e d i)) (safe : ¬RootCycle s q)
    (input : Origin) (authored : input ∈ s.core.origins) (original : OriginRoute s.core input gate.arg.center)
    {actualName : Nat} (atChild : literalUnaryPayloadName406 gate.key input.endpoint = some actualName)
    (payloadBounds : Bounds s.core.current.ordinary ⟨gate.lowerPayload,actualName,gate.upperPayload⟩)
    (noWhere : row.requirements = []) (noOutputs : q.demand.outputs = []) :
    let chosen := preselectAtExactPriorComplete406 trace done i gate safe
    ∃ (invocation : CompletedInvocation406 s q []), invocation.row = row ∧
      HEq invocation.chosen chosen ∧ invocation.actualPayload.center = actualName ∧
      Summarizes (.selected invocation.row.id []) (.selected (.node row.id [])) ∧
      ∃ ledger : ScopedLedger406 s q (.node row.id []),
        GroundedReplayOn406 (.completed invocation) ledger ∧
        ledger.visitRoot = some invocation.visits ∧
        ∀ m, Fits s m → CompletedInvocationMeaning406 invocation m ∧ ScopedEvidence406 s m q (.node row.id []) := by
  let chosen := preselectAtExactPriorComplete406 trace done i gate safe
  change ∃ invocation : CompletedInvocation406 s q [], invocation.row = row ∧
    HEq invocation.chosen chosen ∧ invocation.actualPayload.center = actualName ∧ _
  let payload : OriginalPayload406 chosen := ⟨input,authored,original,actualName,atChild,payloadBounds⟩
  have absent : ∀ index : Fin q.demand.outputs.length, False := by
    intro index
    obtain ⟨n,invalid⟩ := index
    simp [noOutputs] at invalid
  let body : CompletedBody406 payload := ⟨fun i => (absent i).elim⟩
  have kids : frameWhereKids400 (originalNativeFrame406 chosen payload) = [] := by
    simp [frameWhereKids400,AuthoredBodyFrame393.clauses,originalNativeFrame406,frameAtSource395,noWhere,children]
  let invocation : CompletedInvocation406 s q [] :=
    ⟨row,_,exactPriorComplete406 trace done i,chosen,payload,body,fun i => (absent i).elim,
      by simp [LiteralVariableWhere403,noWhere],kids.symm ▸ .nil⟩
  have summary : Summarizes (.selected invocation.row.id []) (.selected (.node row.id [])) :=
    .selected .nil (.selected rfl)
  obtain ⟨ledger,grounded,sound⟩ := actual_scoped_trace_assembles_one_ledger406
    (.completed invocation) summary
  refine ⟨invocation,rfl,HEq.rfl,rfl,summary,ledger,grounded,?_,
    fun m fit => ⟨completed_invocation_means_one_state_and_model406 invocation m fit,(sound m fit).2⟩⟩
  obtain ⟨ds,whereTree,equal,ledgerAt,_,_,_⟩ := grounded
  have eq : ds = [] := (Dictionary.node.inj equal).2
  subst ds
  cases equal
  rw [ledgerAt]
  rfl

/-- The same preselected root can use original installed typed output
rows and exact independently chosen ordered where children. From
typing alone its fixed targets do *not* follow. -/
theorem build_native_invocation_with_exact_body_and_where406 {s q row needs forest ds}
    (chosen : PreselectedUnary406 s q row (needs := needs) forest)
    (payload : OriginalPayload406 chosen)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : NamedInputAtStoredHead401 s.b6 (originalNativeFrame406 chosen payload))
    (retained : ∀ body : CompletedBody406 payload, body.Fixed)
    (literalWhere : LiteralVariableWhere403 row)
    {ts : List Tree}
    (whereActual : WhereForest PriorSource406 s (frameWhereKids400 (originalNativeFrame406 chosen payload)) ts)
    (whereSelected : All₂ Summarizes ts (ds.map Result.selected)) :
    ∃ invoked : CompletedInvocation406 s q ts,
      invoked.row = row ∧ HEq invoked.chosen chosen ∧ HEq invoked.actualPayload payload ∧
      ScopedClassifies406 s q (.selected (.node row.id ds)) ∧
      ∃ ledger : ScopedLedger406 s q (.node row.id ds),
        GroundedReplayOn406 (.completed invoked) ledger ∧
        ∀ m, Fits s m → ledger.Means m ∧ ScopedEvidence406 s m q (.node row.id ds) := by
  obtain ⟨body⟩ := original_completed_native_body_reads_B6406 payload declared typed
  let invoked : CompletedInvocation406 s q ts :=
    ⟨row,needs,forest,chosen,payload,body,retained body,literalWhere,whereActual⟩
  have selected : Summarizes (.selected invoked.row.id ts) (.selected (.node row.id ds)) :=
    .selected whereSelected (.selected rfl)
  exact ⟨invoked,rfl,HEq.rfl,HEq.rfl,completed_invocation_gives_source_verdict406 invoked selected,
    actual_scoped_trace_assembles_one_ledger406 (.completed invoked) selected⟩

end Yulang.GeneralDeclarativeI65.I72
