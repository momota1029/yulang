import Yulang.GeneralMixedCompoundPointSpine307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralMixedCompoundPointRoot307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot interpretation)
open GeneralDictionaryCompoundSource238 (registry declaration declaration_checked)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedContext extendedSnapshot)
open GeneralMixedCompoundPointSpine307 (Slots spine sites centers)
open GeneralMixedCompoundRefreshBound307 (Run models)
open GeneralMixedCompoundUpperRefresh307 (models_iff)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters (Plan rootSite)
open GeneralNominalRecursiveCandidates (arguments report Context)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalReportErasure (erase interval)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

variable (ctx : Context) (coords : Slots ctx)

theorem located : arguments ctx (inputs root) = some [(coords.a,coords.a)] := by
  change GeneralCandidateBoundaryParts.locate ctx.state.base [(0,0)] = _
  rw [GeneralDictionaryRefinedLocations.locate_cons]
  have here := (sourceSlot_exact ctx.state.base 0 coords.a).mpr coords.name_a
  rw [here]
  rfl

include coords in
theorem query : GeneralNominalInspection.queries ctx.state ctx.interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := by
  unfold GeneralNominalInspection.queries
  rw [coords.catalogue_eq,coords.interpretation_eq]
  exact GeneralDictionaryCompoundRoot239.query

theorem report_exact : report ctx declaration [(coords.a,coords.a)] =
    { inspected := [(coords.a,coords.a)],
      checked := [(coords.a,coords.a),(coords.a,coords.a),
        (coords.c,coords.c),(coords.c,coords.c)],
      captures := [⟨0,(coords.c,coords.c),some (.nominal (.source 0) 0 0)⟩,
        ⟨0,(coords.c,coords.c),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(coords.c,coords.c)),
        (.nominal (.source 0) 0 1,(coords.c,coords.c))] } := by
  have baseName : ctx.state.base.source (coords.a) = 0 := coords.name_a
  unfold report
  rw [query ctx coords]
  simp [inspectMany,inspect,coords.read_a,typeArguments,Report.append,Report.visit,
    GeneralMixedCompoundPointSpine307.descriptor,baseName]

abbrev packet : Packet roles :=
  ⟨registry,ctx,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,
    [(coords.a,coords.a)]⟩

abbrev plan : Plan roles := ⟨packet ctx coords,rootSite snapshot.seed root,rfl⟩

theorem same_read : Same (plan ctx coords) GeneralDictionaryCompoundRoot239.plan := by
  refine ⟨rfl,rfl,rfl,coords.seed_eq,coords.catalogue_eq,coords.interpretation_eq,?_⟩
  change erase ctx.state (report ctx declaration [(coords.a,coords.a)]) =
    erase extendedSnapshot (report extendedContext declaration [(0,0)])
  rw [report_exact ctx coords,GeneralDictionaryCompoundRoot239.report_exact]
  have first : ctx.state.base.source (coords.a) = 0 := coords.name_a
  have second : ctx.state.base.source (coords.c) = 2 := coords.name_c
  simp [erase,interval,first,second,GeneralDictionaryCompoundBase239.source]

theorem frame_plan {s : State roles} (run : Run n s) (coords : Slots s.core.erased.current.context)
    {p : Plan roles} (framed : GeneralNominalVersionedEvidence231.Frame registry s.core root key p) :
    p = plan s.core.erased.current.context coords := by
  rcases p with ⟨⟨reg,c,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : c = s.core.erased.current.context := framed.context_eq
  have declEq : decl = declaration := List.mem_singleton.mp framed.visible
  have siteEq : site = GeneralNominalDemandMerging.pointSite root :=
    GeneralDictionaryCompoundSites238.root_raw (sites run ▸ framed.raw_recorded) framed.occurrence_eq
  have centerEq : input = rootSite snapshot.seed root :=
    GeneralDictionaryCompoundSites238.root_center (centers run ▸ framed.center_recorded)
      (inputEq.trans framed.occurrence_eq)
  subst reg; subst c; subst decl; subst site; subst input
  have boundsEq : [(coords.a,coords.a)] = bounds :=
    Option.some.inj ((located s.core.erased.current.context coords).symm.trans framed.located)
  subst bounds
  rfl

theorem no_packet {s : State roles} (run : Run n s) (coords : Slots s.core.erased.current.context)
    (m : Assignment) (valid : Models s m) : ¬ Holds (plan s.core.erased.current.context coords) m := by
  intro held
  have atAnchor := (models_iff m).mp ((models run m).mp valid)
  exact GeneralDictionaryCompoundObstruction239.no_current_packet m atAnchor
    (GeneralDeferredLadderTransport302.held_of_reindex (same_read _ coords) m held atAnchor.1.1)

theorem no_install {s : State roles} (run : Run n s) (e : Effect roles)
    (enabled : Installable registry s e) (focusRoot : e.plan.packet.site.occurrence = root) : False := by
  obtain ⟨coords⟩ := spine run
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,focusRoot] at frame
  have eq := frame_plan run coords frame
  obtain ⟨m,valid,packet,_⟩ := enabled.common
  rw [eq] at packet
  exact no_packet run coords m valid packet

end Yulang.GeneralMixedCompoundPointRoot307
