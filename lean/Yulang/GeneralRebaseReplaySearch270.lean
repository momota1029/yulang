import Yulang.GeneralRebaseReplayScript270

namespace Yulang.GeneralRebaseReplaySearch270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralSourceState (Output)
open GeneralRebaseReplayCommand270 (Command run)
open GeneralRebaseReplayScript270 (Script first)
open GeneralRebaseWeakProgress268 (Lull Weak)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {start : State roles}

abbrev Schedule (registry : Registry) (root : Occurrence roles) :=
 (current : State roles) → List (Command registry root current)

abbrev Replay (registry : Registry) (root : Occurrence roles) (start : State roles) :=
 Σ stop, Script registry root start stop

def prepend (cmd : Command registry root start) (program : Replay registry root (run cmd)) :
 Replay registry root start :=
 ⟨program.1,.execute cmd program.2⟩

/-- All listed prefixes of length at most fuel; no test of an undecidable
original transition predicate is involved. Voluntarily passed commands
carry checked guards; the enumeration may omit genuine commands. -/
def explore (schedule : Schedule registry root) :
 (fuel : Nat) → (current : State roles) → List (Replay registry root current)
 | 0, current => [⟨current,.done current⟩]
 | fuel+1, current => ⟨current,.done current⟩ ::
   (schedule current).flatMap (fun cmd => (explore schedule fuel (run cmd)).map (prepend cmd))

/-- Finite set of admitted old command sequences (not all old sequences). -/
inductive Admitted (schedule : Schedule registry root) :
 Nat → (start : State roles) → Replay registry root start → Prop where
 | done (fuel : Nat) (start : State roles) : Admitted schedule fuel start ⟨start,.done start⟩
 | more {start : State roles} (cmd : Command registry root start) (listed : cmd ∈ schedule start)
   (suffix : Replay registry root (run cmd)) :
   Admitted schedule fuel (run cmd) suffix → Admitted schedule (fuel+1) start (prepend cmd suffix)

theorem enumerate_exact (schedule : Schedule registry root) (fuel : Nat) (start : State roles)
 (program : Replay registry root start) :
 program ∈ explore schedule fuel start ↔ Admitted schedule fuel start program := by
 induction fuel generalizing start with
 | zero =>
   constructor
   · intro listed
     cases List.mem_singleton.mp listed
     exact .done _ _
   · intro seq
     cases seq
     exact List.mem_singleton_self _
 | succ fuel ih =>
   constructor
   · intro listed
     rcases List.mem_cons.mp listed with rfl | later
     · exact .done _ _
     · obtain ⟨cmd,visible,comesFrom⟩ := List.mem_flatMap.mp later
       obtain ⟨suffix,sub,rfl⟩ := List.mem_map.mp comesFrom
       exact .more cmd visible suffix ((ih _ _).mp sub)
   · intro admitted
     cases admitted with
     | done => exact List.mem_cons_self
     | more cmd listed suffix admitted =>
       exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨cmd,listed,List.mem_map.mpr ⟨suffix,(ih _ _).mpr admitted,rfl⟩⟩)

def search (schedule : Schedule registry root) (fuel : Nat) (start : State roles)
 (owners : List Nat) (pool : List Output) : Option {after : State roles // Weak registry root owners pool start after} :=
 (explore schedule fuel start).findSome? (fun program => first owners pool program.2)

theorem hit (schedule : Schedule registry root) (fuel : Nat) (start : State roles)
 (owners : List Nat) (pool : List Output) {witness : {after : State roles // Weak registry root owners pool start after}} (found : search schedule fuel start owners pool = some witness) :
 ∃ program, Admitted schedule fuel start program ∧ first owners pool program.2 = some witness := by
 obtain ⟨_,program,_,splitList,here,_⟩ := List.findSome?_eq_some_iff.1 found
 have listed : program ∈ explore schedule fuel start := by
   rw [splitList]
   exact List.mem_append_right _ List.mem_cons_self
 exact ⟨program,(enumerate_exact schedule fuel start program).mp listed,here⟩

theorem exhaustive_on_schedule (schedule : Schedule registry root) (fuel : Nat) (start : State roles)
 (owners : List Nat) (pool : List Output) (absent : search schedule fuel start owners pool = none)
 (program : Replay registry root start) (valid : Admitted schedule fuel start program) :
 Lull registry root owners pool start program.1 := by
 have no := (List.findSome?_eq_none_iff.1 absent) program ((enumerate_exact schedule fuel start program).mpr valid)
 exact GeneralRebaseReplayScript270.no_hit owners pool program.2 no

/-- A conditional completeness statement expressed against original
transitions rather than the implementation's list of scripts. -/
inductive Within (registry : Registry) (root : Occurrence roles) : Nat → State roles → State roles → Prop where
 | done (fuel : Nat) (start : State roles) : Within registry root fuel start start
 | more {a b c : State roles} (next : Step registry root a b) :
   Within registry root fuel b c → Within registry root (fuel+1) a c

def Covers (schedule : Schedule registry root) : Prop :=
 ∀ a b, Step registry root a b → ∃ cmd ∈ schedule a, run cmd = b

theorem represent_within (schedule : Schedule registry root) (support : Covers schedule)
 (bounded : Within registry root fuel start stop) :
 ∃ program : Replay registry root start, Admitted schedule fuel start program ∧ program.1 = stop := by
 induction bounded with
 | done fuel s => exact ⟨⟨s,.done s⟩,.done fuel s,rfl⟩
 | more next _ ih =>
   obtain ⟨cmd,listed,rfl⟩ := support _ _ next
   obtain ⟨p,valid,rfl⟩ := ih
   exact ⟨prepend cmd p,.more cmd listed p valid,rfl⟩

theorem none_rules_out_bounded_weak (schedule : Schedule registry root) (support : Covers schedule)
 (fuel : Nat) (start stop : State roles) (owners : List Nat) (pool : List Output)
 (absent : search schedule fuel start owners pool = none) (bounded : Within registry root fuel start stop) :
 ¬ Weak registry root owners pool start stop := by
 obtain ⟨pr,admitted,rfl⟩ := represent_within schedule support bounded
 have quiet := exhaustive_on_schedule schedule fuel start owners pool absent pr admitted
 intro hit
 have less := GeneralRebaseWeakProgress268.decrease hit
 rw [GeneralRebaseWeakProgress268.lull_same quiet] at less
 exact (Nat.lt_irrefl _) less

end Yulang.GeneralRebaseReplaySearch270
