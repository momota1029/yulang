import Yulang.GeneralDeclarativeI65I74OriginalRoster485
import Yulang.GeneralDeclarativeI65I74CandidateSignedPath485

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead readPrecheckedHead)
open ObservationAlternatives473 (Positions oldPosition readTermAt)
open Producer479 (Site)

structure OriginalArgumentStart486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n) (visibleOrdinal argument : Nat)
    (site : Fin n) where
  ordinal : Nat
  head : PrecheckedHead (p := p.old) gd
  cell : OriginalRosterCell485 p visibleOrdinal (ordinal,head.orig.declaration)
  address : head.orig.location = ⟨visibleOrdinal,argument⟩
  exactArity : head.orig.declaration.head.length = p.old.root.demand.arguments.length
  root : oldPosition pos site = .logical head.orig.capture.lower
  term : GeneralNominalCenteredHeadMatExpressions.Expr
  actualTerm : readTermAt p.old.state.core pos site = some term

def OriginalArgumentStart486.site
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {i a : Nat} {j : Fin n} (w : OriginalArgumentStart486 p gd pos i a j) :
    Site p.old.state.core pos :=
  ⟨j,w.head.orig.original,w.head.orig.code,w.term,w.actualTerm⟩

def readOriginalArgumentStart486 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (visibleOrdinal argument : Nat) (site : Fin n) :
    Option (OriginalArgumentStart486 p gd pos visibleOrdinal argument site) :=
  match known : rosterCell485 p visibleOrdinal with
  | none => none
  | some (ord,d) => do
    let head ← readPrecheckedHead (p := p.old) gd ⟨visibleOrdinal,argument⟩
    if address : head.orig.location = ⟨visibleOrdinal,argument⟩ then
      if agrees : head.orig.declaration = d then
        if count : head.orig.declaration.head.length = p.old.root.demand.arguments.length then
          if point : oldPosition pos site = .logical head.orig.capture.lower then
            match term : readTermAt p.old.state.core pos site with
            | none => none
            | some actual =>
              some ⟨ord,head,agrees.symm ▸ (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mp known,
                address,count,point,actual,term⟩
          else none
        else none
      else none
    else none

theorem independently_checked_arg_start_replays_at_exact_original_roster_and_demand_coordinate486
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {i a : Nat} {coord : Fin n}
    (w : OriginalArgumentStart486 p gd pos i a coord) :
    readOriginalArgumentStart486 p gd pos i a coord = some w := by
  have reg := (roster_cell_reads_exactly_its_two_original_slots485 _ _ _).mpr w.cell
  have known := PreparedDeclarations463.each_prechecked_head_position_replays gd w.head
  rw [w.address] at known
  unfold readOriginalArgumentStart486
  split
  · rename_i absent
    rw [reg] at absent
    cases absent
  · rename_i ord row seen
    have same := Option.some.inj (seen.symm.trans reg)
    cases same
    simp only [known,bind,Option.bind,w.address,dite_true,w.exactArity,w.root]
    split
    · rename_i absent
      rw [w.actualTerm] at absent
      cases absent
    · rename_i word read
      have exact := Option.some.inj (read.symm.trans w.actualTerm)
      subst word
      cases w
      rfl

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
