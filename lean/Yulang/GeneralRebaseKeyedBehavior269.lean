import Yulang.FiniteBehaviorCheckedRun269
import Yulang.GeneralRebaseBehavior269

namespace Yulang.GeneralRebaseKeyedBehavior269
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseLiveProjection264 (project)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseWeakProgress268 (Weak)
open FiniteBehaviorKeyGraph269 (Graph valid compile Realizes rank)
open FiniteBehaviorDriver269 (drive)
open FiniteRankBehavior269 (Code)

def run (g : Graph n (List Fact)) (fuel : Nat) (start : Fin n) : Option (Nat × Code (List Fact)) :=
 if valid g && decide (rank g start ≤ fuel) then some (drive fuel (compile g fuel start)) else none

/-- A supplied finite key graph determines real weak behavior exactly from
every concrete representative, whereas a projected observer alone need
not preserve that behavior. This theorem checks the graph's rank, but the
realization contract is not checked by the rank test. -/
theorem run_sound (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (g : Graph n (List Fact)) (cost : g.cost = List.length) (key : State roles → Fin n)
 (contract : Realizes g key (fun source => (project owners pool source).remaining) (Weak registry root owners pool))
 (fuel : Nat) (source : State roles) (outcome : run g fuel (key source) = some result) :
 ∃ last, B4Target.Steps (Step registry root) source last ∧
   (project owners pool last).remaining = result.2.label ∧
   (∀ future, B4Target.Steps (Step registry root) last future → project owners pool future = project owners pool last) ∧
   result.1 + (project owners pool last).remaining.length ≤ (project owners pool source).remaining.length := by
 unfold run at outcome
 split at outcome
 · rename_i ok
   have checked := (Bool.and_eq_true ..).mp ok
   have equal := Option.some.inj outcome
   have enough : rank g (key source) ≤ fuel := of_decide_eq_true checked.2
   obtain ⟨last,trace,observation,quiet,budget⟩ := FiniteBehaviorCheckedRun269.from_checked_graph
     g checked.1 key _ _ contract fuel source enough
   refine ⟨last,GeneralRebaseBehavior269.trace_old trace,equal ▸ observation,
     (GeneralRebaseWeakTerminal268.terminal_iff registry root owners pool last).mp quiet,?_⟩
   rw [←equal,contract.label last,contract.label source]
   simpa only [rank,cost] using budget
 · cases outcome

end Yulang.GeneralRebaseKeyedBehavior269
