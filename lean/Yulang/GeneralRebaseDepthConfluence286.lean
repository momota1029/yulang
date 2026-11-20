import Yulang.GeneralRebaseDepthPreSharp286

/-! Same-assignment observational confluence for the actual nested-output fixture.
This is a quotient by complete model and readback observations, not raw state equality. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthConfluence286
open GeneralDictionaryOutputDepth252 (roles root registry sourceRegistry initial)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalVersionedMixedSourceBoundary234 (Local)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthFullTrace286 (Crosses)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck FinalTypeCheck)

def ReadbackSame (s t : State roles) : Prop :=
  (∀ m, Models s m ↔ Models t m) ∧
  ∀ m (p : Payload), Models s m ∧ Evidence registry s.core m root p ↔
    Models t m ∧ Evidence registry t.core m root p

theorem post_same {s t : State roles} (a : GeneralRebaseDepthPhase286.Post s)
    (b : GeneralRebaseDepthPhase286.Post t) : ReadbackSame s t :=
  ⟨fun m => (GeneralRebaseDepthPostQueries286.models a m).trans
    (GeneralRebaseDepthPostQueries286.models b m).symm,
   fun m p => (GeneralRebaseDepthPostQueries286.concrete a m p).trans
    (GeneralRebaseDepthPostQueries286.concrete b m p).symm⟩

theorem maximal_same {s t : State roles} {left right : Nat}
    (a : ActualPath initial s left) (b : ActualPath initial t right)
    (noLeft : ∀ next, ¬ Step registry root s next)
    (noRight : ∀ next, ¬ Step registry root t next) : ReadbackSame s t :=
  post_same
    (GeneralRebaseDepthFullTrace286.crosses_post (GeneralRebaseDepthFullTrace286.maximal_crosses a noLeft))
    (GeneralRebaseDepthFullTrace286.crosses_post (GeneralRebaseDepthFullTrace286.maximal_crosses b noRight))

theorem completion_same {s t : State roles} {left right : Nat}
    (a : ActualPath initial s left) (b : ActualPath initial t right) :
    ∃ sFinal tFinal i j, ActualPath s sFinal i ∧ ActualPath t tFinal j ∧
      left + i ≤ 3 ∧ right + j ≤ 3 ∧ Stable registry sFinal root ∧
      Stable registry tFinal root ∧ ReadbackSame sFinal tFinal ∧
      Local sourceRegistry sFinal root (.selected 0 []) ∧ Local sourceRegistry tFinal root (.selected 0 []) := by
  obtain ⟨sf,i,sp,si,sc,ss,sl,_⟩ := GeneralRebaseDepthFullTrace286.finishes a
  obtain ⟨tf,j,tp,tj,tc,ts,tl,_⟩ := GeneralRebaseDepthFullTrace286.finishes b
  exact ⟨sf,tf,i,j,sp,tp,si,tj,ss,ts,post_same
    (GeneralRebaseDepthFullTrace286.crosses_post sc) (GeneralRebaseDepthFullTrace286.crosses_post tc),sl,tl⟩

theorem maximal_initial_filter {s : State roles} {n : Nat}
    (whole : ActualPath initial s n) (stops : ∀ next, ¬ Step registry root s next)
    (m : Assignment) (p : Payload) :
    Models s m ∧ Evidence registry s.core m root p ↔ Models initial m ∧
      FinalTypeCheck m ∧ p = .node 0 [] := by
  have after := GeneralRebaseDepthFullTrace286.crosses_post
    (GeneralRebaseDepthFullTrace286.maximal_crosses whole stops)
  have joint := GeneralRebaseDepthPostQueries286.concrete after m p
  constructor
  · intro all
    have checked := joint.mp all
    exact ⟨(GeneralRebaseDepthPreAnchor286.initial_models m).mpr checked.1.1,checked⟩
  · exact fun all => joint.mpr all.2

end Yulang.GeneralRebaseDepthConfluence286
