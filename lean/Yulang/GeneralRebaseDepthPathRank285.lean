import Yulang.GeneralRebaseDepthPathKeep285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseDepthPathRank285
open GeneralDictionaryOutputDepth252 (registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known sources)
open GeneralRebaseDepthPathAnchor285 (Anchor snapshot fresh_position)
open GeneralRebaseDepthPathKeep285 (Kept no_install)

inductive Hop : State roles → State roles → Prop
 | refresh {s : State roles} (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx)
    (n : Nat) (present : n ∈ sources (snapshot s)) (old : ¬ Known (snapshot s) n)
    (new : Known ctx.state n) : Hop s (refresh s ctx)

theorem exact {s t : State roles} (a : Anchor s) (k : Kept s) :
    Step registry root s t ↔ Hop s t := by
 constructor
 · rintro ⟨focus,reachable,action⟩
   have rooted := GeneralNominalVersionedMixedTerminalStable234.generated_only a.sites a.edges reachable
   cases action with
   | administrative kind =>
     cases kind with
     | enqueue _ absent =>
       exact False.elim (absent _ (a.sites ▸ List.mem_singleton_self _) rooted.symm)
     | refresh ctx cert n present old new => exact .refresh ctx cert n present old new
     | equate first last supports supports' same novel =>
       exact False.elim (novel (a.equality first last supports supports' same))
     | reobserve revision _ improves =>
       exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision a.points revision improves)
   | refresh _ ctx cert n present old new => exact .refresh ctx cert n present old new
   | install e enabled novel => exact False.elim (novel (no_install a k e enabled rooted))
   | merge first last f l _ novel =>
     rw [a.centers] at f l
     cases List.mem_singleton.mp f
     cases List.mem_singleton.mp l
     exact False.elim (novel (.refl _))
 · intro hop
   cases hop with
   | refresh ctx cert n present old new =>
     exact ⟨root,.root,.refresh root ctx cert n present old new⟩

theorem anchored {s t : State roles} (a : Anchor s) (k : Kept s) (hop : Hop s t) :
    Anchor t ∧ Kept t := by
  cases hop with
  | refresh ctx cert _ _ _ _ =>
    exact ⟨GeneralRebaseDepthPathAnchor285.next a ctx cert,GeneralRebaseDepthPathKeep285.advance k ctx cert⟩

noncomputable def pending (s : State roles) (n : Nat) : Nat := by
  classical exact if Known (snapshot s) n then 0 else 1

noncomputable def rank (s : State roles) : Nat := pending s 0 + pending s 1

theorem le_two (s : State roles) : rank s ≤ 2 := by
  unfold rank pending
  split <;> split <;> omega

theorem monotone_known {s t : State roles} (preserve : ∀ id, Known (snapshot s) id → Known (snapshot t) id)
    (id : Nat) : pending t id ≤ pending s id := by
  classical
  unfold pending
  by_cases known : Known (snapshot s) id
  · simp only [known,preserve _ known,ite_true,Nat.le_refl]
  · simp only [known,ite_false]
    split <;> omega

theorem drop {s t : State roles} (a : Anchor s) (hop : Hop s t) : rank t < rank s := by
  classical
  cases hop with
  | refresh ctx cert n _ old new =>
    let dest := refresh s ctx
    have strict : pending dest n < pending s n := by
      unfold pending
      change (if Known ctx.state n then 0 else 1) < (if Known (snapshot s) n then 0 else 1)
      simp only [old,new,ite_true,ite_false,Nat.zero_lt_one]
    have zero := monotone_known (t := dest) cert.refines.known 0
    have one := monotone_known (t := dest) cert.refines.known 1
    have whereAt := fresh_position a ctx cert n old new
    change rank dest < rank s
    unfold rank
    rcases whereAt with rfl|rfl <;> omega

theorem accessible {s : State roles} (a : Anchor s) (k : Kept s) :
    Acc (fun after before => Step registry root before after) s := by
  have bounded := (measure rank).wf.apply s
  induction bounded with
  | intro now _ ih =>
    constructor
    intro next taken
    have hop := (exact a k).mp taken
    exact ih next (drop a hop) (anchored a k hop).1 (anchored a k hop).2

theorem actual_accessible : Acc (fun after before => Step registry root before after) installed :=
  accessible GeneralRebaseDepthPathAnchor285.initial GeneralRebaseDepthPathKeep285.start

inductive ActualPath : State roles → State roles → Nat → Prop
 | empty (s : State roles) : ActualPath s s 0
 | more {s t u : State roles} {n : Nat} : ActualPath s t n → Step registry root t u → ActualPath s u (n+1)

theorem path_rank {s t : State roles} {n : Nat} (a : Anchor s) (k : Kept s)
    (path : ActualPath s t n) : (Anchor t ∧ Kept t) ∧ n + rank t ≤ rank s := by
  induction path with
  | empty => exact ⟨⟨a,k⟩,by simp⟩
  | more _ action ih =>
    have hop := (exact ih.1.1 ih.1.2).mp action
    have fall := drop ih.1.1 hop
    exact ⟨anchored ih.1.1 ih.1.2 hop,by omega⟩

theorem all_after_install {t : State roles} {n : Nat} (path : ActualPath installed t n) :
    n ≤ 2 ∧ (∀ m, Models t m ↔ Models installed m) := by
  have trace := path_rank GeneralRebaseDepthPathAnchor285.initial GeneralRebaseDepthPathKeep285.start path
  have bound := le_two installed
  exact ⟨by omega,trace.1.1.models⟩

end Yulang.GeneralRebaseDepthPathRank285
