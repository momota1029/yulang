import Yulang.GeneralRebaseConcreteEntries267

namespace Yulang.GeneralRebaseConcreteScan267
open GeneralNominalVersionedJournal232 (State)
open GeneralSourceState (Output)
open GeneralRebaseConcreteEntries267 (Entry entries)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseCheckedWrite259 (commit accepted)
open GeneralRebaseScheduler259

def scan (owners : List Nat) (pool : List Output) (state : State roles) :
 List (Entry registry root state) → Except (List Fact) (Option (Entry registry root state))
 | [] => .ok none
 | first :: rest =>
   match commit (project owners pool state) first.facts with
   | .error missing => .error missing
   | .ok none => scan owners pool state rest
   | .ok (some _) => .ok (some first)

def abstractResult (owners : List Nat) (pool : List Output) (state : State roles) :
 Except (List Fact) (Option (Entry registry root state)) →
 Except (List Fact) (Option (GeneralRebaseStep258.State (GeneralRebaseCompression266.Basis owners pool)))
 | .error missing => .error missing
 | .ok result => .ok (result.map (fun entry => project owners pool entry.after))

theorem scan_commutes (owners : List Nat) (pool : List Output) (state : State roles)
 (choices : List (Entry registry root state)) :
 abstractResult owners pool state (scan owners pool state choices) =
 GeneralRebaseScheduler259.scan (project owners pool state) (choices.map Entry.facts) := by
 induction choices with
 | nil => rfl
 | cons first rest ih =>
   simp only [scan,List.map_cons,GeneralRebaseScheduler259.scan]
   cases h : commit (project owners pool state) first.facts with
   | error missing => rfl
   | ok option =>
     cases option with
     | none => exact ih
     | some target =>
       have accepted := (accepted _ _ _).mp h
       have targetEq := (GeneralRebaseStep258.tryWrite_exact ..).mp accepted.2
       change Except.ok (some (project owners pool first.after)) = Except.ok (some target)
       rw [←first.square owners pool,←targetEq.1]

end Yulang.GeneralRebaseConcreteScan267
