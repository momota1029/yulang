import Yulang.GeneralRebaseReplaySearch270

namespace Yulang.GeneralRebaseReplayFrontier270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseReplayCommand270 (Command run)
open GeneralRebaseReplayScript270 (Script first)
open GeneralRebaseReplaySearch270 (Replay prepend)
open GeneralRebaseWeakProgress268 (Lull Weak)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

/-- Explicit finite proof-carrying frontier. Different branches may offer
different commands even when some states happen to be semantically
equal; no decision on journal equality is needed. -/
def Frontier (registry : Registry) (root : Occurrence roles) : Nat → State roles → Type
 | 0, _ => Unit
 | n+1, start => List (Σ cmd : Command registry root start, Frontier registry root n (run cmd))

def traces : (fuel : Nat) → (start : State roles) → Frontier registry root fuel start →
 List (Replay registry root start)
 | 0, start, _ => [⟨start,.done start⟩]
 | n+1, start, frontier => ⟨start,.done start⟩ ::
   frontier.flatMap (fun branch => (traces n (run branch.1) branch.2).map (prepend branch.1))

def fromSchedule (schedule : GeneralRebaseReplaySearch270.Schedule registry root) :
 (fuel : Nat) → (s : State roles) → Frontier registry root fuel s
 | 0, _ => ()
 | n+1, s => (schedule s).map (fun cmd => ⟨cmd,fromSchedule schedule n (run cmd)⟩)

theorem fromSchedule_traces (schedule : GeneralRebaseReplaySearch270.Schedule registry root)
 (fuel : Nat) (s : State roles) :
 traces fuel s (fromSchedule schedule fuel s) = GeneralRebaseReplaySearch270.explore schedule fuel s := by
 induction fuel generalizing s with
 | zero => rfl
 | succ n ih =>
   simp only [traces,fromSchedule,GeneralRebaseReplaySearch270.explore,List.flatMap_map,ih]

def search (fuel : Nat) (start : State roles) (frontier : Frontier registry root fuel start)
 (owners : List Nat) (pool : List Output) : Option {after : State roles // Weak registry root owners pool start after} :=
 (traces fuel start frontier).findSome? (fun program => first owners pool program.2)

theorem fromSchedule_search (schedule : GeneralRebaseReplaySearch270.Schedule registry root)
 (fuel : Nat) (start : State roles) (owners : List Nat) (pool : List Output) :
 search fuel start (fromSchedule schedule fuel start) owners pool =
   GeneralRebaseReplaySearch270.search schedule fuel start owners pool := by
 simp [search,GeneralRebaseReplaySearch270.search,fromSchedule_traces]

theorem no_visible_advance (fuel : Nat) (start : State roles) (frontier : Frontier registry root fuel start)
 (owners : List Nat) (pool : List Output) (absent : search fuel start frontier owners pool = none)
 (program : Replay registry root start) (listed : program ∈ traces fuel start frontier) :
 Lull registry root owners pool start program.1 :=
 GeneralRebaseReplayScript270.no_hit owners pool program.2 ((List.findSome?_eq_none_iff.1 absent) _ listed)

/-- No returned step is justified by a mere candidate flag: the actual
old weak action is carried by the result, and this lemma recovers the
supplied transcript selecting it. -/
theorem certificate (fuel : Nat) (start : State roles) (frontier : Frontier registry root fuel start)
 (owners : List Nat) (pool : List Output)
 {witness : {after : State roles // Weak registry root owners pool start after}}
 (chosen : search fuel start frontier owners pool = some witness) :
 ∃ program ∈ traces fuel start frontier, first owners pool program.2 = some witness := by
 obtain ⟨_,p,_,splitList,found,_⟩ := List.findSome?_eq_some_iff.1 chosen
 exact ⟨p,by rw [splitList]; exact List.mem_append_right _ List.mem_cons_self,found⟩

end Yulang.GeneralRebaseReplayFrontier270
