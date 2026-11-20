import Yulang.GeneralMixedCompoundPointChild307
import Yulang.GeneralMixedCompoundPointEquality307
import Yulang.GeneralMixedCompoundBatch307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 10500000
namespace Yulang.GeneralMixedCompoundPointExact307
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundSites238 (raw_sites)
open GeneralMixedCompoundRefreshBound307 (Run models bound)
open GeneralMixedCompoundPointSpine307 (reach sites centers point_closed)
open GeneralMixedCompoundTail307 (registered raw_not_novel no_merge)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedRefresh232 (refresh)

theorem decompose {s t : State roles} (path : Run n s) (move : Step registry root s t) :
    ∃ (ctx : GeneralNominalRecursiveCandidates.Context)
      (_ : GeneralNominalVersionedMixedObservations233.Refresh s ctx)
      (id : Nat), id ∈ GeneralMixedCompoundRefreshBound307.pool s ∧
      ¬ GeneralMixedCompoundRefreshBound307.k s id ∧ GeneralNominalState.Known ctx.state id ∧
      t = refresh s ctx := by
  obtain ⟨focus,generated,op⟩ := move
  have seen := (sites path).trans raw_sites
  have crossed := (centers path).trans GeneralDictionaryCompoundSites238.centers
  have which := registered (reach path) seen generated
  cases op with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,present,eq⟩ := raw_not_novel seen which
      exact False.elim (absent site present eq)
    | refresh ctx cert id present unknown known =>
      exact ⟨ctx,cert,id,present,unknown,known,rfl⟩
    | equate first last supported other same fresh =>
      exact False.elim (fresh (GeneralMixedCompoundPointEquality307.closed path first last supported other same))
    | reobserve revision certificate improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision
        (point_closed path) revision improves)
  | refresh focus ctx cert id present unknown known =>
    exact ⟨ctx,cert,id,present,unknown,known,rfl⟩
  | install e enabled _ =>
    rcases which with rootHere|childHere
    · exact False.elim (GeneralMixedCompoundPointRoot307.no_install path e enabled rootHere)
    · exact False.elim (GeneralMixedCompoundPointChild307.no_install path e enabled childHere)
  | merge a b first last same fresh =>
    have agree : Models s = Models upperState := funext (fun m => propext (models path m))
    exact False.elim (fresh (no_merge agree crossed first last same))

theorem every_step {s t : State roles} (path : Run n s) (move : Step registry root s t) :
    Run (n+1) t := by
  obtain ⟨ctx,cert,id,present,unknown,known,rfl⟩ := decompose path move
  exact .more path ctx cert id present unknown known

theorem raw_score_lt {s t : State roles} (path : Run n s) (move : Step registry root s t) :
    GeneralMixedCompoundRefreshBound307.score s < GeneralMixedCompoundRefreshBound307.score t := by
  obtain ⟨ctx,cert,id,present,unknown,known,rfl⟩ := decompose path move
  exact GeneralMixedCompoundRefreshBound307.score_lt path ctx cert id present unknown known

inductive RawRun : Nat → State roles → Prop
  | zero : RawRun 0 point
  | more {n s t} : RawRun n s → Step registry root s t → RawRun (n+1) t

theorem exact_run {s : State roles} : RawRun n s ↔ Run n s := by
  constructor
  · intro p
    induction p with
    | zero => exact .zero
    | more _ step ih => exact every_step ih step
  · intro p
    induction p with
    | zero => exact .zero
    | more _ ctx cert id present unknown known ih =>
      exact .more ih ⟨root,.root,.refresh root ctx cert id present unknown known⟩

theorem arbitrary_raw_bound {s : State roles} (p : RawRun n s) : n ≤ 3 :=
  bound (exact_run.mp p)

theorem all_maximal_length_stop {s t : State roles} (p : RawRun 3 s) :
    ¬ Step registry root s t := by
  intro more
  have four := arbitrary_raw_bound (.more p more)
  omega

theorem exact_lengths_to_verified_halt (n : Nat) :
    RawRun n upperState ↔ n = 1 ∨ n = 2 ∨ n = 3 :=
  exact_run.trans (GeneralMixedCompoundBatch307.feasible_exact n)

end Yulang.GeneralMixedCompoundPointExact307
