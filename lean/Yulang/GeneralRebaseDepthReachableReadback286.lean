import Yulang.GeneralRebaseDepthPreEvidence286

/-! Preserve the type/row distinction of 285 for every actual reachable raw
snapshot. Canonical inflation computes the output; it does not license
replacing the original assignment in a raw model claim. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthReachableReadback286
open GeneralDictionaryOutputDepth252 (roles registry root initial)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPublic285 (SourceTypes project inflate basic)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck FinalTypeCheck)
open GeneralRebaseDepthPreEvidence286 (same_joint_everywhere)
open GeneralRebaseDepthPhase286 (Pre Post)

def Public (s : State roles) (types : SourceTypes) (payload : Payload) : Prop :=
    ∃ m : Assignment, project m = types ∧ Models s m ∧ Evidence registry s.core m root payload

theorem public_exact {s : State roles} {steps : Nat} (path : ActualPath initial s steps)
    (types : SourceTypes) (payload : Payload) :
    Public s types payload ↔ InitialTypeCheck (basic types (fun _ => Common.rowEmpty)) ∧
      payload = .node 0 [] := by
  apply Iff.trans ?_ (GeneralRebaseDepthView285.projected_exact types payload)
  exact exists_congr (fun m => and_congr_right (fun _ =>
    (same_joint_everywhere path m payload).trans (GeneralRebaseDepthPayload285.same_assignment_exact m payload).symm))

theorem public_inflation {s : State roles} {steps : Nat} (path : ActualPath initial s steps)
    (types : SourceTypes) (payload : Payload) (rows : Nat → Common.Row) :
    Public s types payload ↔ Models s (inflate types rows) ∧
      Evidence registry s.core (inflate types rows) root payload := by
  let m := inflate types rows
  have equivalence : Public s types payload ↔ GeneralRebaseDepthView285.projected types payload :=
    (public_exact path types payload).trans (GeneralRebaseDepthView285.projected_exact types payload).symm
  exact equivalence.trans ((GeneralRebaseDepthView285.arbitrary_rows types payload rows).trans
    ((GeneralRebaseDepthPayload285.same_assignment_exact m payload).trans (same_joint_everywhere path m payload).symm))

theorem canonical_from_initial {s : State roles} {steps : Nat} (path : ActualPath initial s steps)
    (m : Assignment) (p : Payload) :
    (let data := inflate (project m) (fun i => (m i).2)
     Models s data ∧ Evidence registry s.core data root p) ↔ Models initial m ∧ p = .node 0 [] := by
  let data := inflate (project m) (fun i => (m i).2)
  exact (same_joint_everywhere path data p).trans
    ((GeneralRebaseDepthPayload285.same_assignment_exact data p).symm.trans
      ((GeneralRebaseDepthPayload285.canonical_exact m p).trans
        (and_congr_left (fun _ => (GeneralRebaseDepthPreAnchor286.initial_models m).symm))))

theorem strict_raw_filter {s t : State roles} (pre : Pre s) (post : Post t) :
    (∀ m, Models t m → Models s m) ∧
      ∃ m, Models s m ∧ ¬ Models t m := by
  constructor
  · intro m after
    exact (pre.anchor.models m).mpr ((GeneralRebaseDepthPostQueries286.models post m).mp after).1
  · let m := GeneralDictionaryOutputDepthInstall252.smallModel
    refine ⟨m,(pre.anchor.models m).mpr ((GeneralRebaseDepthGroundModels285.source_inputs m).mp
      GeneralDictionaryOutputDepthInstall252.small_source),?_⟩
    intro after
    exact GeneralRebaseDepthMinimal285.scalar_ne_output ((GeneralRebaseDepthPostQueries286.models post m).mp after).2

end Yulang.GeneralRebaseDepthReachableReadback286
