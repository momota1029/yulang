import Yulang.GeneralMixedCompoundAnyRefresh307
import Yulang.GeneralDictionaryCompoundObstruction239
import Yulang.GeneralDeferredLadderTransport302
import Yulang.GeneralDictionaryRefinedLocations

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralMixedCompoundAnyRoot307
open GeneralDictionaryJournalRefinement228Source (roles root snapshot interpretation)
open GeneralDictionaryCompoundSource238 (registry declaration declaration_checked)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedContext extendedSnapshot pointDesc)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedRefresh232 (refresh)
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

variable (ctx : Context) (cert : Refresh refreshed ctx)

abbrev emb (i : Fin 7) := cert.refines.base.embed i

theorem original_argument : arguments extendedContext (inputs root) = some [(0,0)] := by decide +kernel

theorem located : arguments ctx (inputs root) = some [(emb ctx cert 0,emb ctx cert 0)] :=
  GeneralDictionaryRefinedLocations.arguments extendedContext ctx cert.refines _ _ original_argument

theorem rename_point :
    ctx.state.nominals (emb ctx cert 0) =
    some (GeneralNominalRefinements.renameDescriptor (emb ctx cert) pointDesc) :=
  cert.refines.nominals (0 : Fin 7) pointDesc rfl

include cert in
theorem query : GeneralNominalInspection.queries ctx.state ctx.interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := by
  unfold GeneralNominalInspection.queries
  rw [cert.refines.constructors,cert.interpretation]
  exact GeneralDictionaryCompoundRoot239.query

theorem report_exact : report ctx declaration [(emb ctx cert 0,emb ctx cert 0)] =
    { inspected := [(emb ctx cert 0,emb ctx cert 0)],
      checked := [(emb ctx cert 0,emb ctx cert 0),(emb ctx cert 0,emb ctx cert 0),
        (emb ctx cert 2,emb ctx cert 2),(emb ctx cert 2,emb ctx cert 2)],
      captures := [⟨0,(emb ctx cert 2,emb ctx cert 2),some (.nominal (.source 0) 0 0)⟩,
        ⟨0,(emb ctx cert 2,emb ctx cert 2),some (.nominal (.source 0) 0 1)⟩],
      anchors := [(.nominal (.source 0) 0 0,(emb ctx cert 2,emb ctx cert 2)),
        (.nominal (.source 0) 0 1,(emb ctx cert 2,emb ctx cert 2))] } := by
  have baseName : ctx.state.base.source (emb ctx cert 0) = 0 := cert.refines.base.source (0 : Fin 7)
  unfold report
  rw [query ctx cert]
  simp [inspectMany,inspect,rename_point ctx cert,typeArguments,Report.append,Report.visit,
    GeneralNominalRefinements.renameDescriptor,GeneralNominalRefinements.renameParameter,
    pointDesc,baseName] <;> rfl

abbrev packet : Packet roles :=
  ⟨registry,ctx,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,
    [(emb ctx cert 0,emb ctx cert 0)]⟩

abbrev plan : Plan roles := ⟨packet ctx cert,rootSite snapshot.seed root,rfl⟩

theorem same_read : Same (plan ctx cert) GeneralDictionaryCompoundRoot239.plan := by
  refine ⟨rfl,rfl,rfl,cert.refines.seed,cert.refines.constructors,cert.interpretation,?_⟩
  change erase ctx.state (report ctx declaration [(emb ctx cert 0,emb ctx cert 0)]) =
    erase extendedSnapshot (report extendedContext declaration [(0,0)])
  rw [report_exact ctx cert,GeneralDictionaryCompoundRoot239.report_exact]
  have first : ctx.state.base.source (emb ctx cert 0) = 0 := cert.refines.base.source (0 : Fin 7)
  have second : ctx.state.base.source (emb ctx cert 2) = 2 := cert.refines.base.source (2 : Fin 7)
  simp [erase,interval,first,second,GeneralDictionaryCompoundBase239.source]

theorem frame_plan {p : Plan roles} (framed : GeneralNominalVersionedEvidence231.Frame
    registry (refresh refreshed ctx).core root key p) : p = plan ctx cert := by
  rcases p with ⟨⟨reg,s,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : s = ctx := framed.context_eq
  have declEq : decl = declaration := List.mem_singleton.mp framed.visible
  have siteEq : site = GeneralNominalDemandMerging.pointSite root :=
    GeneralDictionaryCompoundSites238.root_raw framed.raw_recorded framed.occurrence_eq
  have inputSame : input = rootSite snapshot.seed root :=
    GeneralDictionaryCompoundSites238.root_center framed.center_recorded (inputEq.trans framed.occurrence_eq)
  subst reg; subst s; subst decl; subst site; subst input
  have boundsEq : [(emb ctx cert 0,emb ctx cert 0)] = bounds :=
    Option.some.inj ((located ctx cert).symm.trans framed.located)
  subst bounds
  rfl

theorem no_packet (m : Assignment) (valid : Models (refresh refreshed ctx) m) :
    ¬ Holds (plan ctx cert) m := by
  intro held
  have old := (refresh_models cert).mp valid
  have before := GeneralNominalRefinements.models cert.refines m held.1
  exact GeneralDictionaryCompoundObstruction239.no_current_packet m old
    (GeneralDeferredLadderTransport302.held_of_reindex (same_read ctx cert) m held before)

include cert in
theorem no_install (e : Effect roles) (enabled : Installable registry (refresh refreshed ctx) e)
    (rootFocus : e.plan.packet.site.occurrence = root) : False := by
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,rootFocus] at frame
  have direct := frame_plan ctx cert frame
  obtain ⟨m,valid,held,_⟩ := enabled.common
  rw [direct] at held
  exact no_packet ctx cert m valid held

end Yulang.GeneralMixedCompoundAnyRoot307
