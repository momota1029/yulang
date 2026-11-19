import Yulang.GeneralRebaseKeyedWeakObserver268
import Yulang.GeneralRebaseClosedObserver259

namespace Yulang.GeneralRebaseKeyedWeakScheduler268
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStutterKeys268 (Keys Valid visit)
open GeneralRebaseKeyedWeakObserver268 (Contract observe observe_current step_iff terminal_iff)
open GeneralRebaseWeakProgress268 (Weak Counted)
open GeneralRebaseWeakTerminal268 (Terminal)
open GeneralRebaseStep258 (Proposal)
open GeneralRebaseScheduler259 (next next_step terminal)
open GeneralRebaseCompression266 (Basis)

theorem closed (k : Keys n roles) (offers : Fin n → List Proposal) (source : State roles)
 (supported : ∀ key ∈ visit k source, ∀ p ∈ offers key, p ⊆ Basis owners pool) :
 GeneralRebaseClosedObserver259.Closed (observe k offers source owners pool) := by
 intro state p listed
 unfold observe at listed
 split at listed
 · obtain ⟨key,visited,offered⟩ := List.mem_flatMap.mp listed
   exact supported key visited p offered
 · cases listed

theorem some_sound (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (offers : Fin n → List Proposal) (contract : Contract registry root owners pool k region offers)
 (source : State roles) (allowed : region source) (target : GeneralRebaseStep258.State (Basis owners pool))
 (result : next (observe k offers source owners pool) (project owners pool source) = .ok (some target)) :
 ∃ after, Weak registry root owners pool source after ∧ project owners pool after = target :=
 (step_iff k valid offers contract source allowed target).mp (next_step _ _ _ result)

theorem none_sound (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (offers : Fin n → List Proposal) (contract : Contract registry root owners pool k region offers)
 (source : State roles) (allowed : region source)
 (result : next (observe k offers source owners pool) (project owners pool source) = .ok none) :
 Terminal registry root owners pool source := by
 rw [GeneralRebaseWeakTerminal268.terminal_iff]
 exact (terminal_iff k valid offers contract source allowed).mp (terminal _ _ result)

/-- The scheduler chooses the projected update. The proof chooses a matching
concrete witness, then recomputes observations there. No frozen-table reuse,
and no executable extraction of the concrete witnesses, is asserted. -/
theorem recomputed_completion (k : Keys n roles) (valid : Valid registry root owners pool k region)
 (offers : Fin n → List Proposal) (contract : Contract registry root owners pool k region offers)
 (support : ∀ source, region source → ∀ key ∈ visit k source, ∀ p ∈ offers key, p ⊆ Basis owners pool)
 (preserve : ∀ before after, region before → Weak registry root owners pool before after → region after)
 (source : State roles) (allowed : region source) :
 ∃ final count, Counted registry root owners pool count source final ∧ region final ∧
 next (observe k offers final owners pool) (project owners pool final) = .ok none ∧
 Terminal registry root owners pool final ∧
 count + (project owners pool final).remaining.length ≤ (project owners pool source).remaining.length := by
 have completed : ∃ final count, Counted registry root owners pool count source final ∧
      region final ∧ next (observe k offers final owners pool) (project owners pool final) = .ok none := by
   induction source using (GeneralRebaseWeakProgress268.wellFounded registry root owners pool).induction with
   | h source ih =>
     cases h : next (observe k offers source owners pool) (project owners pool source) with
     | error missing =>
       exact False.elim
         (GeneralRebaseClosedObserver259.next_no_error _ (closed k offers source (support source allowed)) _ missing h)
     | ok answer =>
       cases answer with
       | none => exact ⟨source,0,.nil _,allowed,h⟩
       | some target =>
         obtain ⟨middle,advance,_⟩ := some_sound k valid offers contract source allowed target h
         obtain ⟨final,count,trace,inRegion,done⟩ := ih middle advance (preserve source middle allowed advance)
         exact ⟨final,count+1,GeneralRebaseWeakTerminal268.prepend advance trace,inRegion,done⟩
 obtain ⟨final,count,trace,inRegion,done⟩ := completed
 exact ⟨final,count,trace,inRegion,done,none_sound k valid offers contract final inRegion done,
   GeneralRebaseWeakProgress268.budget trace⟩

end Yulang.GeneralRebaseKeyedWeakScheduler268
