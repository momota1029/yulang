import Yulang.GeneralDeclarativeI65I74TypedFocusHop482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions oldPosition)
open GeneralDeclarativeWitnessOrigins350 (Table)
open Producer479 (Site Trail TrailWire readTrail)
open LiteralVisits473 (StepWire Checkpoint)
open InputCoordinates475 (SourceIndexPair478)

inductive FocusedChain {n : Nat} {p : FullProblem} {pos : Positions n} (table : Table) :
    Site p.old.state.core pos → ReadCard → List (StepWire × Checkpoint n) →
      Site p.old.state.core pos → ReadCard → List (Option SourceIndexPair478) → Prop where
  | stop : FocusedChain table here card [] here card []
  | step (one : FocusedCardHop (p := p) table here action card chosen.which) :
      FocusedChain table one.after one.childCard rest last terminal orderedRows →
      FocusedChain table here card ((action,chosen)::rest) last terminal (one.chosenSource::orderedRows)

structure FocusResult {n : Nat} {p : FullProblem} {pos : Positions n} (table : Table)
    (here : Site p.old.state.core pos) (card : ReadCard) (moves : List (StepWire × Checkpoint n)) where
  finish : Site p.old.state.core pos
  selected : ReadCard
  reads : List (Option SourceIndexPair478)
  trail : FocusedChain (p := p) table here card moves finish selected reads

def readFocusedChain {n : Nat} {p : FullProblem} {pos : Positions n} (table : Table)
    (here : Site p.old.state.core pos) (card : ReadCard) (moves : List (StepWire × Checkpoint n)) :
    Option (FocusResult (p := p) table here card moves) :=
  match moves with
  | [] => some ⟨here,card,[],.stop⟩
  | (action,chosen)::rest => do
    let step ← readFocusedCardHop (p := p) table here action card chosen.which
    let tail ← readFocusedChain table step.after step.childCard rest
    pure ⟨tail.finish,tail.selected,step.chosenSource::tail.reads,.step step tail.trail⟩

theorem recorded_focus_count_matches_exact_old_move_count
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table}
    {here : Site p.old.state.core pos} {card : ReadCard} {moves finish selected reads}
    (t : FocusedChain (p := p) table here card moves finish selected reads) :
    reads.length = moves.length := by
  induction t with
  | stop => rfl
  | step _ _ ih => simp [ih]

/-- Run the existing signed check and compare the exact chosen terminal.
Source cards are selected by the same ordered moves, not substituted
checkpoints, and the old signed policy is unchanged. -/
structure PinnedSignedFocus {n : Nat} {p : FullProblem} {pos : Positions n} (table : Table)
    (here : Site p.old.state.core pos) (card : ReadCard) (rel : List (Fin n × Fin n)) (w : TrailWire n) where
  focus : FocusResult (p := p) table here card w.tail
  bit : Bool
  signed : readTrail rel here w = some (focus.finish,bit)

private def withCheck {A : Type} (o : Option A) : Option {a // o = some a} :=
  match o with | none => none | some found => some ⟨found,rfl⟩

def readPinnedSignedFocus {n : Nat} {p : FullProblem} {pos : Positions n} (table : Table)
    (here : Site p.old.state.core pos) (card : ReadCard) (rel : List (Fin n × Fin n)) (w : TrailWire n) :
    Option (PinnedSignedFocus (p := p) table here card rel w) := do
  let focus ← readFocusedChain (p := p) table here card w.tail
  let signed ← withCheck (readTrail rel here w)
  if same : signed.val.1.index = focus.finish.index then
    if q : GeneralDeclarativeWitnessLiteral349.eqExpr signed.val.1.query focus.finish.query = true then
      if st : signed.val.1.pattern = focus.finish.pattern then
        have query := (GeneralDeclarativeWitnessLiteral349.eq_expr ..).mp q
        have site : signed.val.1 = focus.finish := by
          cases a : signed.val.1 with
          | mk i pat code raw exact =>
            cases b : focus.finish with
            | mk j pt c rw got =>
              simp only [a,b] at same query st
              subst j; subst c; subst pt
              have rawEq := Option.some.inj (exact.symm.trans got)
              subst rw
              rfl
        have result : signed.val = (focus.finish,signed.val.2) := Prod.ext site rfl
        some ⟨focus,signed.val.2,result ▸ signed.property⟩
      else none
    else none
  else none

theorem pinned_signed_focus_reflects_same_trail_and_every_read
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table}
    {here : Site p.old.state.core pos} {card : ReadCard} {rel : List (Fin n × Fin n)}
    {w : TrailWire n} (r : PinnedSignedFocus (p := p) table here card rel w) :
    Trail p.old.state.core pos rel here (w.tail.map Prod.fst) (w.tail.map (fun x => x.2.which))
      r.focus.finish r.bit ∧
    FocusedChain (p := p) table here card w.tail r.focus.finish r.focus.selected r.focus.reads :=
  ⟨(Producer479.finite_trail_wire_reflects_exact_selected_path479 r.signed).2,r.focus.trail⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
