import Yulang.GeneralMixedCompoundUpperRefresh307
import Yulang.GeneralDictionaryCompoundFailure239
import Yulang.GeneralMixedCompoundChildHidden307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralMixedCompoundUpperChild307
open GeneralDictionaryJournalRefinement228Source (roles root interpretation)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralMixedCompoundUpperSnapshot307 (context snap)
open GeneralMixedCompoundUpperBase307 (viewHeads upper)
open GeneralMixedCompoundUpperRefresh307 (upperState step models_iff)
open GeneralNominalVersionedCandidates231 (inputs Failed Prepared Survivor InspectionPending)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalRecursiveInspection
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)

theorem located : arguments context (inputs childSite.occurrence) = some [(5,6)] := by decide +kernel

theorem query : GeneralNominalInspection.queries snap interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] :=
  GeneralDictionaryCompoundChild239.query

theorem report_exact : report context declaration [(5,6)] =
    { inspected := [(5,6)], checked := [(5,6),(5,6)], conflicts := [(5,6)] } := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,viewHeads]

theorem fresh : GeneralNominalVersionedAllocation231.Fresh snap registry childSite.occurrence.identity [] := by
  intro key present hit
  have projected := GeneralMixedCompoundUpperSnapshot307.support _ hit
  exact GeneralDictionaryCompoundFailure239.fresh key present projected

theorem failed : Failed registry context childSite.occurrence declaration := by
  refine ⟨GeneralDictionaryCompoundSource238.source.metadata,[(5,6)],located,?_,?_,?_,?_⟩
  · rw [report_exact]; exact fresh
  · rw [report_exact]
  · rw [report_exact]
  · exact Or.inl (by rw [report_exact]; intro h; cases h)

theorem known : ¬ GeneralNominalState.RootPending snap childSite.occurrence.demand := by
  intro pending
  exact GeneralDictionaryCompoundFailure239.known
    (GeneralNominalRefinements.pending_backwards GeneralMixedCompoundUpperSnapshot307.refineRaw _ pending)

theorem no_inspection_pending : ¬ InspectionPending registry context childSite.occurrence := by
  rintro ⟨_,d,visible,_,bad,_⟩
  cases List.mem_singleton.mp visible
  exact bad failed

theorem no_prepared : ¬ Prepared registry context childSite.occurrence declaration := by
  rintro ⟨_,_,bounds,here,_,done,_⟩
  have eq : bounds = [(5,6)] := Option.some.inj (here.symm.trans located)
  subst bounds
  rw [report_exact] at done
  exact (by cases done.2.1)

theorem no_survivor (key : Nat) (children : List (Occurrence roles)) :
    ¬ Survivor registry context childSite.occurrence key children := by
  rintro ⟨_,d,visible,_,_,_,_,_,prepared,_⟩
  cases List.mem_singleton.mp visible
  exact no_prepared prepared

theorem no_frame (key : Nat) (plan : Plan roles) :
    ¬ GeneralNominalVersionedEvidence231.Frame registry upperState.core childSite.occurrence key plan := by
  intro framed
  have key : plan.packet.declaration = declaration := List.mem_singleton.mp framed.visible
  have prepared := framed.prepared
  rw [key] at prepared
  exact no_prepared prepared

theorem no_evidence (m : Assignment) (payload : GeneralDictionaryReadback.Payload) :
    ¬ GeneralNominalVersionedEvidence231.Evidence registry upperState.core m childSite.occurrence payload := by
  intro ev
  have indexed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ev
  cases indexed with
  | node instanceProof _ =>
    obtain ⟨p,framed⟩ := instanceProof
    exact no_frame _ p framed.frame

theorem reachable : B4TargetV8.Reachable
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root upperState := by
  obtain ⟨before,start,trace⟩ := GeneralDictionaryCompoundRefreshStep239.reachable
  exact ⟨before,start,.tail trace step⟩

theorem same_request :
    GeneralSourceState.Output.mk 0 4 ∈ GeneralNominalCenteredHeadOutputs.requests upperState.core root :=
  (GeneralNominalVersionedRefresh232.refresh_requests refreshed context).mpr
    GeneralMixedCompoundChildHidden307.root_request_retained

end Yulang.GeneralMixedCompoundUpperChild307
