import Yulang.GeneralDeclarativeI65I74ProducerCheckpoint479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open ObservationAlternatives473 (Positions oldPosition graphOf readTermAt anchorFor)
open CommonRoleRegularGraph (successors)
open LiteralVisits473 (Checkpoint readCheck read_checkpoint_guards readLiteralVisitStep
  independent_step_derivation_replays_its_original_addresses StepWire childSlot)

def siteAt {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (i : Fin n) (p : GeneralDeclarationPatterns.Pattern)
    (q : GeneralNominalCenteredHeadMatExpressions.Expr) : Option (Site s pos) :=
  match term : readTermAt s pos i with
  | none => none
  | some actual => some ⟨i,p,q,actual,term⟩

theorem siteAt_replays479 {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (site : Site s pos) : siteAt site.index site.pattern site.query = some site := by
  rcases site with ⟨_,_,_,_,exactTerm⟩
  unfold siteAt
  split
  · rename_i missing
    rw [exactTerm] at missing
    cases missing
  · rename_i found hit
    have only := Option.some.inj (hit.symm.trans exactTerm)
    subst found
    rfl

/-- Read exactly the supplied next constructor, not arbitrary successors or
the children below an unselected branch. Each source action is linked to
the old physical place, and no old graph mutation occurs. -/
def readHop {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (here : Site s pos) (move : StepWire) (next : Fin n) : Option (Site s pos) := do
  let typed ← readLiteralVisitStep s here.pattern here.query here.term move
  if anchorFor (pos.cells.get here.index) (childSlot move.action) typed.actualRawChild =
      oldPosition pos next ∧ next ∈ successors (graphOf s pos) here.index then
    siteAt next typed.writtenChild typed.childQuery
  else none

theorem exact_hop_has_a_unique_replay479
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {here next : Site s pos} {move}
    (one : Hop here next move) :
    readHop here move next.index = some next := by
  simp [readHop,independent_step_derivation_replays_its_original_addresses one.typed,
    one.position,one.edge,one.written,one.query,siteAt_replays479,bind,Option.bind]

theorem reified_hop_keeps_the_same_old_place479
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {here next : Site s pos} {move i}
    (run : readHop here move i = some next) :
    i = next.index ∧ Nonempty (Hop here next move) := by
  unfold readHop at run
  cases stepRead : readLiteralVisitStep s here.pattern here.query here.term move with
  | none => simp [stepRead] at run
  | some typed =>
    simp only [stepRead,bind,Option.bind] at run
    split at run
    · rename_i condition
      unfold siteAt at run
      split at run
      · cases run
      · rename_i term termExact
        have same := Option.some.inj run
        subst next
        exact ⟨rfl,⟨⟨typed,rfl,rfl,condition.1,condition.2⟩⟩⟩
    · cases run

structure TrailWire (n : Nat) where
  cursor : Checkpoint n
  tail : List (StepWire × Checkpoint n)

def readTrailAux {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (here : Site s pos) (cursor : Checkpoint n)
    (steps : List (StepWire × Checkpoint n)) : Option (Site s pos × Bool) :=
  if cursor.which = here.index then
    match readCheck s pos rel (oldPosition pos here.index) cursor with
    | none => none
    | some sign =>
      match steps with
      | [] => some (here,sign)
      | (move,next)::rest =>
        if sign then none
        else do
          let reached ← readHop here move next.which
          readTrailAux rel reached next rest
  else none

def readTrail {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    (rel : List (Fin n × Fin n)) (here : Site s pos) (w : TrailWire n) :
    Option (Site s pos × Bool) :=
  readTrailAux rel here w.cursor w.tail

theorem finite_trail_wire_replays_exact_selected_path479
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel}
    {here moves indices final bit}
    (path : Trail s pos rel here moves indices final bit) :
    ∃ w : TrailWire n, w.cursor.which = here.index ∧
      w.tail.map Prod.fst = moves ∧ w.tail.map (fun x => x.2.which) = indices ∧
      readTrail rel here w = some (final,bit) := by
  induction path with
  | @stop here bit guard meaning =>
    obtain ⟨check,loc,ran⟩ := LiteralVisits473.independent_checkpoint_reifies_the_exact_site_and_sign guard bit meaning
    refine ⟨⟨check,[]⟩,loc,rfl,rfl,?_⟩
    rw [readTrail,readTrailAux]
    simp [loc,ran]
  | @step here next finish move moves positions bit hop guard safe rest ih =>
    obtain ⟨after,loc,movesExact,positionsExact,replay⟩ := ih
    obtain ⟨check,hereExact,rootRead⟩ := LiteralVisits473.independent_checkpoint_reifies_the_exact_site_and_sign
      guard false (by simp [safe])
    refine ⟨⟨check,(move,after.cursor)::after.tail⟩,hereExact,by simp [movesExact],by simp [loc,positionsExact],?_⟩
    rw [readTrail,readTrailAux]
    simp only [hereExact,ite_true,rootRead,bind,Option.bind,loc,exact_hop_has_a_unique_replay479 hop]
    cases after
    exact replay

private theorem read_aux_reflects479
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel}
    (here : Site s pos) (cursor : Checkpoint n) (steps : List (StepWire × Checkpoint n))
    {final bit} (run : readTrailAux rel here cursor steps = some (final,bit)) :
    cursor.which = here.index ∧
      Trail s pos rel here (steps.map Prod.fst) (steps.map (fun x => x.2.which)) final bit := by
  induction steps generalizing here cursor with
  | nil =>
    rw [readTrailAux] at run
    split at run
    · rename_i loc
      cases replay : readCheck s pos rel (oldPosition pos here.index) cursor with
      | none => simp [replay] at run
      | some sign =>
        simp only [replay,Option.some.injEq,Prod.mk.injEq] at run
        obtain ⟨rfl,rfl⟩ := run
        obtain ⟨guard,_,meaning⟩ := read_checkpoint_guards replay
        rw [loc] at guard meaning
        exact ⟨loc,.stop guard meaning⟩
    · cases run
  | cons next rest ih =>
    rcases next with ⟨move,cp⟩
    rw [readTrailAux] at run
    split at run
    · rename_i loc
      cases replay : readCheck s pos rel (oldPosition pos here.index) cursor with
      | none => simp [replay] at run
      | some sign =>
        cases sign with
        | true => simp [replay] at run
        | false =>
          simp only [replay,bind,Option.bind] at run
          cases advance : readHop here move cp.which with
          | none => simp [advance] at run
          | some next =>
            rw [advance] at run
            have after := (ih next cp run).2
            obtain ⟨arrival,⟨hop⟩⟩ := reified_hop_keeps_the_same_old_place479 advance
            obtain ⟨guard,_,meaning⟩ := read_checkpoint_guards replay
            rw [loc] at guard meaning
            have safe : ¬ QuotientObservation471.ReturnsUpToEquality (graphOf s pos) here.index :=
              fun yes => Bool.false_ne_true (meaning.mpr yes)
            simpa only [List.map_cons,arrival] using And.intro loc (Trail.step hop guard safe after)
    · cases run

theorem finite_trail_wire_reflects_exact_selected_path479
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel}
    {here : Site s pos} {w : TrailWire n} {final bit}
    (run : readTrail rel here w = some (final,bit)) :
    w.cursor.which = here.index ∧
      Trail s pos rel here (w.tail.map Prod.fst) (w.tail.map (fun x => x.2.which)) final bit :=
  read_aux_reflects479 here w.cursor w.tail run

end Yulang.GeneralDeclarativeI65.I72.Producer479
