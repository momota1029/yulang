import Yulang.GeneralDeferredLadderAfterPromotion302
import Yulang.GeneralDeferredLadderTrace302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralDeferredLadderReindexed302
open GeneralDeferredLadderLedger302 (Phase env)
open GeneralDeferredLadderReport302 (context nominal_at)
open GeneralDeferredLadderRefresh302 (promotedPhase)
open GeneralDeferredLadderRefreshHead302 (terminal_has_no_nominal)
open GeneralObservedLadderReport301 (pos)
open GeneralObservedLadderRoute301 (focus site)
open GeneralObservedLadderJournalRows301 (rawRow attached)
open GeneralObservedLadderJournalCompiler301 (probe receipt)
open GeneralObservedLadderObserver301 (finish reject)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalRefinements (renameDescriptor)
open GeneralDeclarationExamples (display)
open GeneralNominalExamples (intDisplay interpretation)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (arguments report Context)
open GeneralNominalUnaryCaptureFacts (captured report_exact)
open GeneralGeneratedDictionaryRun299 (Entry)

theorem query_list (ctx : Context) (shape : ctx.state.constructors = GeneralDeclarationExamples.constructors)
    (interp : ctx.interpretation = interpretation) :
    GeneralNominalInspection.queries ctx.state ctx.interpretation display = [.nominal 0 [.variables [0]]] := by
  unfold GeneralNominalInspection.queries
  rw [shape,interp]
  exact GeneralObservedLadderReport301.display_query 0

theorem query_int (ctx : Context) (interp : ctx.interpretation = interpretation) :
    GeneralNominalInspection.queries ctx.state ctx.interpretation intDisplay = [.scalar .int] := by
  rw [interp]
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,interpretation]

theorem promotion_metadata (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) :
    ctx.state.constructors = GeneralDeclarationExamples.constructors ∧ ctx.interpretation = interpretation := by
  have cs := cert.refines.constructors
  have ci := cert.interpretation
  rw [p.context_eq] at cs ci
  exact ⟨cs,ci⟩

theorem location (ctx : Context) (n i : Nat) (slot : Fin ctx.state.base.slots) (id : ctx.state.base.source slot = i) :
    arguments ctx (focus n i) = some [(slot,slot)] := by
  change GeneralCandidateBoundaryParts.locate ctx.state.base (List.ofFn (fun _ : Fin 1 => (i,i))) = _
  have exact := (GeneralDictionaryBinderLocations.sourceSlot_exact ctx.state.base i slot).mpr id
  simp [List.ofFn_succ,GeneralCandidateBoundaryParts.locate,exact]

theorem probe_exact_list (ctx : Context) (first last : Fin ctx.state.base.slots)
    (located : ctx.state.base.source last = child)
    (desc : GeneralNominalState.Descriptor ctx.state.base.slots)
    (named : desc.declaration.name = 0)
    (seen : ctx.state.nominals first = some desc)
    (point : desc.arguments = [.type (last,last)])
    (qList : GeneralNominalInspection.queries ctx.state ctx.interpretation display = [.nominal 0 [.variables [0]]])
    (qInt : GeneralNominalInspection.queries ctx.state ctx.interpretation intDisplay = [.scalar .int]) :
    probe ctx [(first,first)] = some ⟨1,[child]⟩ := by
  have listExact := report_exact ctx display first desc seen 0 (last,last) point
    (by rwa [named])
  rw [named] at listExact
  have wrong : report ctx intDisplay [(first,first)] =
      { inspected := [(first,first)], checked := [(first,first),(first,first)],
        conflicts := [(first,first)] } := by
    unfold report
    rw [qInt]
    simp [inspectMany,inspect,Report.visit,Report.append,seen]
  unfold probe
  rw [listExact,wrong]
  change (if ctx.state.base.source last = ctx.state.base.source last then
    some (⟨1,[ctx.state.base.source last]⟩ : Entry) else none) = _
  rw [located]
  simp

theorem probe_list_after (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (i : Nat) (hi : i ≤ n) :
    (arguments ctx (focus n i)).bind (probe ctx) = some ⟨1,[i+1]⟩ := by
  let a := pos n i (by omega)
  let b := pos n (i+1) (by omega)
  let d := GeneralNominalOutputGrowthModels.descriptor n a hi
  have source : (env p).state.nominals a = some d := nominal_at n i hi
  have lift := cert.refines
  rw [p.context_eq] at lift
  have exact := lift.nominals a d source
  have first := lift.base.source a
  have last := lift.base.source b
  rw [location ctx n i _ first]
  exact probe_exact_list ctx (lift.base.embed a) (lift.base.embed b) last _ rfl exact rfl
    (query_list ctx (promotion_metadata p ctx cert).1 (promotion_metadata p ctx cert).2)
    (query_int ctx (promotion_metadata p ctx cert).2)

theorem probe_scalar_after (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    (arguments ctx (focus n (n+1))).bind (probe ctx) = some ⟨3,[]⟩ := by
  obtain ⟨slot,identity,_⟩ := GeneralDeferredLadderRefreshHead302.terminal_scalar p ctx cert known
  obtain ⟨scalar,noNominal⟩ := terminal_has_no_nominal p ctx cert known slot identity
  rw [location ctx n (n+1) slot identity]
  change probe ctx [(slot,slot)] = _
  have good : report ctx intDisplay [(slot,slot)] =
      { inspected := [(slot,slot)], checked := [(slot,slot),(slot,slot)] } := by
    unfold report
    rw [query_int ctx (promotion_metadata p ctx cert).2]
    simp [inspectMany,inspect,Report.visit,Report.append,noNominal,scalar]
  have bad : report ctx display [(slot,slot)] =
      { inspected := [(slot,slot)], checked := [(slot,slot),(slot,slot)], conflicts := [(slot,slot)] } := by
    unfold report
    rw [query_list ctx (promotion_metadata p ctx cert).1 (promotion_metadata p ctx cert).2]
    simp [inspectMany,inspect,Report.visit,Report.append,noNominal,scalar]
  unfold probe
  rw [good,bad]
  rfl

theorem promoted_raw_row (p : Phase n k) (ctx : Context) (i : Nat) :
    rawRow (refresh p.state ctx) i = if i ≤ k then some (site n i).observed else none :=
  GeneralObservedLadderJournalRows301.raw_hit (promotedPhase p) i

theorem promoted_attachment (p : Phase n k) (ctx : Context) (i j : Nat) :
    attached (refresh p.state ctx) i j = true ↔ i < k ∧ j = i+1 :=
  GeneralObservedLadderJournalRows301.attached_exact (promotedPhase p) i j

end Yulang.GeneralDeferredLadderReindexed302
