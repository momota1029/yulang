import Yulang.GeneralRebaseDepthPostQueries286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14100000
namespace Yulang.GeneralRebaseDepthFullTrace286
open GeneralDictionaryOutputDepth252 (roles root registry sourceRegistry)
open GeneralRebaseDepthPreAnchor286 (initial)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Hop InstallHop Pre Post)
open GeneralRebaseDepthEnableShape286 (Linked as_pre)
open GeneralRebaseDepthPreAvailable286 (settled_post)

inductive RefreshTrace : State roles → State roles → Nat → Prop
 | empty (s : State roles) : RefreshTrace s s 0
 | more {s t u : State roles} {n : Nat} : RefreshTrace s t n → Hop t u → RefreshTrace s u (n+1)

theorem real_refresh_trace {s t : State roles} {n : Nat} (trace : RefreshTrace s t n) :
    ActualPath s t n := by
  induction trace with
  | empty => exact .empty _
  | more _ hop ih =>
    cases hop with
    | refresh ctx cert id present old new => exact .more ih ⟨root,.root,.refresh root ctx cert id present old new⟩

theorem linked_after {s : State roles} {n : Nat} (earlier : RefreshTrace initial s n) : Linked s := by
  induction earlier with
  | empty => exact GeneralRebaseDepthEnableShape286.initial
  | more _ hop ih => exact GeneralRebaseDepthEnableShape286.hop ih hop

structure Crosses (endState : State roles) (n : Nat) : Prop where
  trace : ∃ (before justInstalled : State roles) (first last : Nat),
    RefreshTrace initial before first ∧ InstallHop before justInstalled ∧
      RefreshTrace justInstalled endState last ∧ n = first+1+last

theorem suffix_post {s t : State roles} {n : Nat} (after : Post s)
    (suffix : RefreshTrace s t n) : Post t := by
  induction suffix with
  | empty => exact after
  | more _ hop ih => exact GeneralRebaseDepthPhase286.post_refresh ih hop

theorem crosses_post {s : State roles} {n : Nat} (hit : Crosses s n) : Post s := by
  obtain ⟨before,justInstalled,first,last,earlier,install,suffix,_⟩ := hit.trace
  have after := GeneralRebaseDepthPhase286.cross (as_pre (linked_after earlier)) install
  exact suffix_post after suffix

theorem decomposes {s : State roles} {n : Nat} (whole : ActualPath initial s n) :
    RefreshTrace initial s n ∨ Crosses s n := by
  induction whole with
  | empty => exact Or.inl (.empty _)
  | more _ chosen prev =>
    rcases prev with quiet|crossed
    · rcases GeneralRebaseDepthPhase286.pre_partition (as_pre (linked_after quiet)) chosen with again|once
      · exact Or.inl (.more quiet again)
      · exact Or.inr ⟨_,_,_,0,quiet,once,.empty _,by simp⟩
    · have hop := GeneralRebaseDepthPhase286.post_step (crosses_post crossed) chosen
      obtain ⟨before,middle,first,last,earlier,once,suffix,number⟩ := crossed.trace
      exact Or.inr ⟨before,middle,first,last+1,earlier,once,.more suffix hop,by omega⟩

theorem maximal_crosses {s : State roles} {n : Nat} (whole : ActualPath initial s n)
    (halted : ∀ next, ¬ Step registry root s next) : Crosses s n := by
  rcases decomposes whole with noInstall|crossed
  · obtain ⟨next,extra⟩ := GeneralRebaseDepthPreAvailable286.offers (linked_after noInstall)
    exact (halted next (GeneralRebaseDepthPhase286.as_step extra)).elim
  · exact crossed

theorem maximal_result {s : State roles} {n : Nat} (whole : ActualPath initial s n)
    (closed : ∀ next, ¬ Step registry root s next) :
    n ≤ 3 ∧ Crosses s n ∧ Local sourceRegistry s root (.selected 0 []) ∧
      B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry s root := by
  have crossed := maximal_crosses whole closed
  have good := crosses_post crossed
  exact ⟨GeneralRebaseDepthFullRank286.complete_bound whole,crossed,
    GeneralRebaseDepthPostQueries286.selected good,GeneralRebaseDepthPostQueries286.evidence_at good⟩

theorem finishes {s : State roles} {n : Nat} (earlier : ActualPath initial s n) :
    ∃ final later, ActualPath s final later ∧ n + later ≤ 3 ∧
      Crosses final (n+later) ∧ Stable registry final root ∧
      Local sourceRegistry final root (.selected 0 []) ∧
      B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry final root := by
  have reached := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) earlier
  have acc := GeneralRebaseDepthFullRank286.accessibility reached
  obtain ⟨t,k,h,halted⟩ := GeneralRebaseDepthPathComplete285.terminates s acc
  have complete := maximal_result (GeneralRebaseDepthPathComplete285.concat earlier h) halted
  exact ⟨t,k,h,complete.1,complete.2.1,
    (GeneralNominalVersionedMixedKernel234.closure halted).1,complete.2.2.1,complete.2.2.2⟩

theorem sharp_path : ActualPath initial GeneralRebaseDepthScalar285.refreshed 3 := by
  have first : ActualPath initial GeneralDictionaryOutputDepthInstall252.installed 1 :=
    .more (.empty _) GeneralDictionaryOutputDepthInstall252.step
  exact GeneralRebaseDepthPathComplete285.concat first GeneralRebaseDepthPathSharp285.two_refreshes

end Yulang.GeneralRebaseDepthFullTrace286
