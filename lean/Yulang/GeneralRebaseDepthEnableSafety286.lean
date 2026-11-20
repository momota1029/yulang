import Yulang.GeneralRebaseDepthEnableShape286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14100000
namespace Yulang.GeneralRebaseDepthEnableSafety286
open GeneralDictionaryOutputDepth252 (roles registry root declaration model snapshot)
open GeneralDictionaryOutputDepthInstall252 (small_source smallModel form form_value)
open GeneralRebaseDepthPreAnchor286 (Anchor)
open GeneralRebaseDepthPrePlan286 (Certified)
open GeneralRebaseDepthEnableShape286 (Linked Shape)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCandidates231 (Survivor Unique)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters (Plan)
open GeneralRebaseDepthPathAnchor285 renaming snapshot → raw

theorem input_known {s : State roles} (a : Anchor s) :
    ¬ GeneralNominalState.RootPending (raw s) root.demand := by
 rintro ⟨_,missing⟩
 obtain ⟨slot,number,desc,cached⟩ := a.nominalTwo
 exact missing ⟨slot,number,Or.inr ⟨desc,cached⟩⟩

theorem world {s : State roles} (a : Anchor s) : Models s smallModel :=
  (a.models _).mpr ((GeneralRebaseDepthGroundModels285.source_inputs _).mp small_source)

theorem no_semantic_cycle {s : State roles} (a : Anchor s) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic s origin :=
  GeneralDictionaryOutputDepthCycles252.acyclic (world a) (fun i => ⟨form i,form_value i⟩) origin

theorem no_raw_cycle {s : State roles} (a : Anchor s) (slot : Fin (raw s).base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt (raw s) slot := by
  intro cycle
  exact no_semantic_cycle a _ (GeneralRebaseRawIntoFull271.recurs s ⟨smallModel,world a⟩ slot cycle)

theorem administrative {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady s root := by
 constructor
 · exact ⟨p.input,v.frame.center_recorded,p.input_exact.trans v.frame.occurrence_eq⟩
 · intro first one _ last two _
   rw [a.centers] at one two
   cases List.mem_singleton.mp one
   cases List.mem_singleton.mp two
   exact .refl _

theorem safe {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry s root := by
 refine ⟨input_known a,?_,?_,?_⟩
 · rintro (rawCycle | (⟨_,cycle⟩ | ⟨_,_,_,_,cycle⟩))
   · obtain ⟨_,_,_,slot,_,cycle⟩ := rawCycle
     exact no_raw_cycle a slot cycle
   · exact no_semantic_cycle a _ cycle
   · exact no_semantic_cycle a _ cycle
 · rintro (rawCycle | ⟨_,_,_,_,cycle⟩)
   · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := rawCycle
     exact no_raw_cycle a visited.1 cycle
   · exact no_semantic_cycle a _ cycle
 · rintro (⟨_,d,visible,_,_,unprepared⟩ | missing)
   · have same := (List.mem_singleton.mp visible).trans (List.mem_singleton.mp v.frame.visible).symm
     exact unprepared (same.symm ▸ v.frame.prepared)
   · exact missing (administrative a v)

theorem cache {s : State roles} (a : Linked s) :
    GeneralNominalVersionedMixedObservations233.CacheSound s (raw s) := by
  intro observation recorded
  refine ⟨[],[],.source,.source,fun m _ supported => ?_⟩
  have yes : GeneralNominalState.Models snapshot m := a.rawSource ▸ supported.1
  have check := (GeneralRebaseDepthGroundModels285.source_inputs m).mp yes
  exact GeneralCanonicalObservations.recorded_sound (raw s) m ((a.anchor.rawModels m).mpr check) recorded

theorem positions {s : State roles} {p : Plan roles} (a : Anchor s) (v : Shape p) :
    GeneralNominalVersionedCycles232.Safe s p :=
  ⟨v.inspections,fun entry _ => no_semantic_cycle a entry.1⟩

theorem survivor {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p) :
    Survivor registry s.core.erased.current.context root 0 [] := by
  have frame := v.frame
  let bounds : List (GeneralNominalInspection.Bounds s.core.erased.current.context.state) :=
    frame.context_eq ▸ p.packet.bounds
  have located := GeneralRebaseDepthPathEvidenceAt285.move_location _ _ frame.context_eq p.packet.bounds frame.located
  refine ⟨input_known a,p.packet.declaration,frame.visible,frame.registry_eq ▸ p.packet.checked,
    frame.key_eq,frame.role_eq,bounds,located,frame.prepared,?_⟩
  symm
  unfold GeneralNominalVersionedCandidates231.children GeneralNominalVersionedFrame231.children
    GeneralDictionaryEmissionPlans.children
  have noReq : p.packet.declaration.requirements = [] := by
    rw [List.mem_singleton.mp frame.visible]
    rfl
  rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ noReq]
  rfl

theorem unique {s : State roles} {p : Plan roles} (a : Anchor s) (v : Certified s p) :
    Unique registry s.core.erased.current.context root 0 [] := by
  have first := survivor a v
  refine ⟨first,?_⟩
  intro key kids other
  have otherCopy := other
  obtain ⟨_,d,visible,_,key_eq,_,_,_,_,_⟩ := other
  cases List.mem_singleton.mp visible
  have equal : key = 0 := key_eq.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional
    GeneralDictionaryOutputDepth252.checked otherCopy first⟩

end Yulang.GeneralRebaseDepthEnableSafety286
