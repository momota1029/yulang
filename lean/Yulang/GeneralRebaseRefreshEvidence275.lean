import Yulang.GeneralRebaseRefreshPrepared275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9100000
namespace Yulang.GeneralRebaseRefreshEvidence275
open GeneralNominalCenters (Plan)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed installed_model effect terminal)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedMixedKernel234 (Step Committed)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralRebaseRefreshFrame275 (of_frame refinement interpretation moved)
open GeneralRebaseRefreshAcc275 (Kept)
open GeneralRebaseRefreshClosure275 (Gates)
open GeneralRebaseRefreshRank275 (Hop)
open GeneralNominalCommonBridge (Assignment)

def Validated (state : State roles) : Prop :=
 ∃ p : Plan roles, Frame registry state.core root declaration.id p ∧ Observed p ∧ Committed state p ∧ Ready state.core root p

theorem initial : Validated installed :=
 ⟨_,GeneralDictionaryVersionedSecondSelected233.frame,
   GeneralRebaseRefreshAcc275.initial_observed,
   GeneralNominalVersionedCommitted232.replay_committed GeneralDictionaryVersionedPointStage233.point effect,
   GeneralNominalVersionedInstalledEvidence233.ready rfl terminal⟩

theorem kept (valid : Validated state) : Kept state := by
 obtain ⟨p,frame,observed,committed,_⟩ := valid
 exact ⟨p,of_frame frame,observed,committed⟩

theorem moved_good {state : State roles} (gates : Gates state) (valid : Validated state)
 (ctx : GeneralNominalCandidates.Context) (cert : Refresh state ctx) :
 Validated (refresh state ctx) := by
 obtain ⟨p,frame,observed,committed,ready⟩ := valid
 let location := of_frame frame
 let ref := refinement location cert
 let q := retarget p ref
 have interp := interpretation location cert
 have nextGates := GeneralRebaseRefreshClosure275.gates_next gates ctx cert
 have model : Models (refresh state ctx) extended :=
   (nextGates.anchor.models extended).mpr installed_model
 have nextFrame : Frame registry (refresh state ctx).core root declaration.id q :=
   GeneralRebaseRefreshPrepared275.rebuild frame observed committed cert extended model
 have newReady := (GeneralNominalVersionedFrameTransport232.ready_iff
   (before := (refresh state ctx).core) (after := state.core)
   (fun _ => GeneralNominalVersionedRefresh232.refresh_requests state ctx)).mpr ready
 refine ⟨q,nextFrame,GeneralRebaseRetarget275.observed p ref interp observed,?_,
   GeneralRebaseRetargetEffects275.ready p ref interp (refresh state ctx).core newReady⟩
 obtain ⟨another,whereAt,_,commits⟩ := GeneralRebaseRefreshAcc275.keep_next
   (state := state) ⟨p,location,observed,committed⟩ ctx cert
 rw [GeneralRebaseRefreshFrame275.same_plan nextGates (of_frame nextFrame) whereAt]
 exact commits

theorem move_hop {state after : State roles} (gates : Gates state) (valid : Validated state)
 (hop : Hop state after) : Gates after ∧ Validated after := by
 cases hop with
 | step ctx cert _ _ _ _ =>
   exact ⟨GeneralRebaseRefreshClosure275.gates_next gates ctx cert,moved_good gates valid ctx cert⟩

theorem all_histories {state : State roles}
 (path : B4Target.Steps (Step registry root) installed state) : Gates state ∧ Validated state := by
 induction path with
 | refl => exact ⟨GeneralRebaseRefreshClosure275.gates_initial,initial⟩
 | tail _ step ih =>
   exact move_hop ih.1 ih.2 ((GeneralRebaseRefreshAcc275.exact_hop ⟨ih.1,kept ih.2⟩).mp step)

theorem leaves {state : State roles} (valid : Validated state) (m : Assignment) (model : Models state m) :
 Evidence registry state.core m root (.node declaration.id []) := by
 obtain ⟨p,frame,_,committed,ready⟩ := valid
 have pack := committed.1 m model
 have effects : GeneralNominalVersionedEffects231.ClassEffects state.core root p m :=
   frame.occurrence_eq ▸ pack.2
 have empty : GeneralNominalVersionedFrame231.children p.packet = [] := by
   unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
   have leaf : p.packet.declaration.requirements = [] := by rw [(of_frame frame).declaration_eq]
   rw [GeneralRebaseRetarget275.no_emission _ _ _ _ _ leaf]
   rfl
 exact GeneralNominalVersionedEvidence231.evidence_leaf
   ⟨p,GeneralNominalVersionedEvidence231.certificate_of_semantics frame empty.symm pack.1 ready effects⟩

theorem all_actual_leaves {state : State roles}
 (path : B4Target.Steps (Step registry root) installed state) (m : Assignment) :
 Models state m ↔ Models installed m ∧ Evidence registry state.core m root (.node declaration.id []) := by
 have all := all_histories path
 constructor
 · intro model
   exact ⟨(all.1.anchor.models m).mp model,leaves all.2 m model⟩
 · intro pair
   exact (all.1.anchor.models m).mpr pair.1

end Yulang.GeneralRebaseRefreshEvidence275
