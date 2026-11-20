import Yulang.GeneralRebaseDepthFullRank286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 13500000
namespace Yulang.GeneralRebaseDepthEnableShape286
open GeneralDictionaryOutputDepth252 (roles plan snapshot root registry)
open GeneralRebaseDepthPreAnchor286 (initial Anchor)
open GeneralRebaseDepthPrePlan286 (Certified)
open GeneralRebaseDepthPhase286 (Pre Hop)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedPlans231 (emittedSchema)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredSteps (inspection)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseNonleafCommitted276 (refinement interpretation result)

structure Shape (p : Plan roles) : Prop where
  emitted : emittedSchema p = emittedSchema plan
  inspections : (inspection p).inspected.length = (inspection p).tests.length

structure Linked (s : State roles) : Prop where
  anchor : Anchor s
  rawSource : s.core.erased.source.state = snapshot
  packets : s.core.erased.current.packets = []
  witness : ∃ p : Plan roles, Certified s p ∧ Shape p

theorem as_pre {s : State roles} (linked : Linked s) : Pre s :=
  ⟨linked.anchor,by obtain ⟨p,cert,_⟩ := linked.witness; exact ⟨p,cert⟩⟩

theorem initial : Linked GeneralRebaseDepthPreAnchor286.initial := by
 have a := GeneralRebaseDepthPreAnchor286.start
 refine ⟨a,rfl,rfl,plan,?_,rfl,by decide +kernel⟩
 exact ⟨GeneralDictionaryOutputDepth252.frame,GeneralRebaseDepthCommit285.seen,
   GeneralDictionaryOutputDepthInstall252.ready,GeneralDictionaryOutputInputs258.inputs,fun _ => Iff.rfl,
   GeneralDictionaryOutputCompletion258.classes,GeneralDictionaryOutputDepth252.children_empty⟩

theorem inspection_transport {s : State roles} {p : Plan roles} (v : Certified s p)
    {ctx : GeneralNominalCandidates.Context} (cert : Refresh s ctx) :
    inspection (result v.frame cert) =
       GeneralNominalSlotReport198.report (refinement v.frame cert).base.embed (inspection p) := by
  let ref := refinement v.frame cert
  have interp := interpretation v.frame cert
  unfold inspection
  change GeneralNominalRecursiveInspection.inspectMany ctx.state
    (GeneralNominalInspection.queries ctx.state ctx.interpretation p.packet.declaration)
    (p.packet.bounds.map (GeneralNominalSlotObservation198.bounds ref.base.embed)) _ _ = _
  rw [show GeneralNominalInspection.queries ctx.state ctx.interpretation p.packet.declaration =
      GeneralNominalInspection.queries p.packet.context.state p.packet.context.interpretation
      p.packet.declaration by simp only [GeneralNominalInspection.queries,interp,ref.constructors]]
  exact GeneralNominalSlotReport198.inspectMany_report ref v.observed _ _

theorem shape_after {s : State roles} {ctx : GeneralNominalCandidates.Context} {p : Plan roles}
    (v : Certified s p) (before : Shape p) (cert : Refresh s ctx) : Shape (result v.frame cert) := by
  constructor
  · exact (GeneralRebaseNonleafRetarget276.emitted_schema_eq p (refinement v.frame cert)
     (interpretation v.frame cert) v.observed).trans before.emitted
  · rw [inspection_transport v cert]
    simpa only [GeneralNominalSlotReport198.report,List.length_map] using before.inspections

theorem refresh_link {s : State roles} {ctx : GeneralNominalCandidates.Context}
    (linked : Linked s) (cert : Refresh s ctx) : Linked (refresh s ctx) := by
  obtain ⟨p,v,shape⟩ := linked.witness
  have new := GeneralRebaseDepthPrePlan286.advance linked.anchor ⟨p,v⟩ ctx cert
  obtain ⟨q,good⟩ := new
  have a := GeneralRebaseDepthPreAnchor286.advance linked.anchor ctx cert
  have targetFrame := GeneralRebaseDepthPrePlan286.frame_next linked.anchor v ctx cert
  have eq := GeneralRebaseDepthPreInstall286.unique_located a
    (GeneralRebaseDepthPathKeep285.of_frame good.frame)
    (GeneralRebaseDepthPathKeep285.of_frame targetFrame)
  subst q
  exact ⟨a,linked.rawSource,linked.packets,_,good,shape_after v shape cert⟩

theorem hop {s t : State roles} (linked : Linked s) (h : Hop s t) : Linked t := by
  cases h with
  | refresh ctx cert _ _ _ _ => exact refresh_link linked cert

end Yulang.GeneralRebaseDepthEnableShape286
