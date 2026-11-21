import Yulang.GeneralMixedCompoundAnyRoot307
import Yulang.GeneralDictionaryCompoundFailure239

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralMixedCompoundAnyChild307
open GeneralDictionaryJournalRefinement228Source (roles)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralDictionaryCompoundSnapshot239 (extendedContext extendedSnapshot)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundAnyRoot307 (emb query)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalRecursiveCandidates (Context arguments report)
open GeneralNominalRecursiveInspection
open GeneralNominalVersionedCandidates231 (inputs Prepared Failed)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalCenters (Plan)

variable (ctx : Context) (cert : Refresh refreshed ctx)

theorem located : arguments ctx (inputs childSite.occurrence) = some [(emb ctx cert 5,emb ctx cert 6)] :=
  GeneralDictionaryRefinedLocations.arguments extendedContext ctx cert.refines _ _
    GeneralDictionaryCompoundChild239.located

theorem no_nominal : ctx.state.nominals (emb ctx cert 5) = none := by
  cases seen : ctx.state.nominals (emb ctx cert 5) with
  | none => rfl
  | some d =>
    have nClass := GeneralMixedCompoundAnyRefresh307.nominal_read ctx cert _ d seen
    have source : ctx.state.base.source (emb ctx cert 5) = lo := cert.refines.base.source (5 : Fin 7)
    rw [source] at nClass
    exact False.elim ((by decide +kernel : ¬ (lo = 0 ∨ lo = 1)) nClass)

theorem lower_known : ctx.state.view.graph (emb ctx cert 5) ≠ .unresolved := by
  have known := cert.refines.known lo GeneralDictionaryCompoundRefreshStep239.lower_known
  obtain ⟨slot,equal,head|⟨d,seen⟩⟩ := known
  · have loc := ctx.state.base.source_injective (equal.trans (cert.refines.base.source (5 : Fin 7)).symm)
    rw [loc] at head
    exact head
  · have loc := ctx.state.base.source_injective (equal.trans (cert.refines.base.source (5 : Fin 7)).symm)
    rw [loc,no_nominal ctx cert] at seen
    cases seen

theorem report_exact : report ctx declaration [(emb ctx cert 5,emb ctx cert 6)] =
    { inspected := [(emb ctx cert 5,emb ctx cert 6)],
      checked := [(emb ctx cert 5,emb ctx cert 6),(emb ctx cert 5,emb ctx cert 6)],
      conflicts := [(emb ctx cert 5,emb ctx cert 6)] } := by
  unfold report
  rw [query ctx cert]
  cases seen : ctx.state.view.heads (emb ctx cert 5) with
  | scalar n => simp [inspectMany,inspect,Report.visit,Report.append,no_nominal ctx cert,seen]
  | structural kind children => simp [inspectMany,inspect,Report.visit,Report.append,no_nominal ctx cert,seen]
  | deferred reason =>
    exact False.elim (lower_known ctx cert (by
      simp [GeneralNormalizedObservation.Snapshot.graph,seen,GeneralNormalizedObservation.Head.node]))

include cert in
theorem no_prepared : ¬ Prepared registry ctx childSite.occurrence declaration := by
  rintro ⟨_,_,bounds,whereAt,_,done,_⟩
  have eq : bounds = [(emb ctx cert 5,emb ctx cert 6)] := Option.some.inj (whereAt.symm.trans (located ctx cert))
  subst bounds
  rw [report_exact ctx cert] at done
  cases done.2.1

include cert in
theorem failed : Failed registry ctx childSite.occurrence declaration := by
  refine ⟨?_,_,located ctx cert,?_,?_,?_,?_⟩
  · let fromSource := GeneralDictionaryCompoundSource238.source.metadata
    refine ⟨cert.refines.constructors.symm,?_⟩
    intro name ty lookup
    have original := fromSource.2 name ty
    exact original (cert.interpretation ▸ lookup)
  · rw [report_exact ctx cert]
    intro key mem hit
    rw [cert.refines.seed] at hit
    have own := GeneralDictionaryCompoundFailure239.fresh key mem (cert.support _ hit)
    exact cert.refines.allocated _ own
  · rw [report_exact ctx cert]
  · rw [report_exact ctx cert]
  · exact Or.inl (by rw [report_exact ctx cert]; intro h; cases h)

include cert in
theorem no_frame (key : Nat) (p : Plan roles) :
    ¬ GeneralNominalVersionedEvidence231.Frame registry (refresh refreshed ctx).core childSite.occurrence key p := by
  intro frame
  have eq : p.packet.declaration = declaration := List.mem_singleton.mp frame.visible
  have prep := frame.prepared
  rw [eq] at prep
  exact no_prepared ctx cert prep

include cert in
theorem no_install (e : Effect roles) (enabled : Installable registry (refresh refreshed ctx) e)
    (focusChild : e.plan.packet.site.occurrence = childSite.occurrence) : False := by
  have frame := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq,focusChild] at frame
  exact no_frame ctx cert _ e.plan frame

end Yulang.GeneralMixedCompoundAnyChild307
