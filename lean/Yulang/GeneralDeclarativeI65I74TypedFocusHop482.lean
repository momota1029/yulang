import Yulang.GeneralDeclarativeI65I74AuthoredFullRead482
import Yulang.GeneralDeclarativeI65I74ScopedRouteSound480

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open CommonRoleCanonicalRows (Row)
open Producer479 (Site Hop readHop)
open LiteralVisits473 (StepWire ReadStep readLiteralVisitStep)
open WrittenPattern460 (Address)
open ObservationAlternatives473 (Positions oldPosition)
open RetainedFull445 (FullProblem)
open InputCoordinates475 (rawAt SourceIndexPair478)
open GeneralNominalMaterialization (Mode)

def argumentCard : ReadCards → Nat → Option ReadCard
  | .nil,_ => none
  | .cons chosen _,0 => some chosen
  | .cons _ later,k+1 => argumentCard later k

def fieldCard (label : Nat) : Row Expr → ReadCards → Option ReadCard
  | (key,_)::rest,.cons chosen later =>
    if key = label then some chosen else fieldCard label rest later
  | _,_ => none

/-- A focus selector on an already checked typing card. It does not
open a child (especially not a join or a capture) or check a sibling. -/
def subCard (action : Address) : ReadCard → Option ReadCard
  | .expose _ next => subCard action next
  | .variant next => match action with | .tag _ => some next | _ => none
  | .primitive args | .nominal args => match action with
    | .arg atArg => argumentCard args atArg
    | _ => none
  | .record _ _ written _ members _ => match action with
    | .field label => fieldCard label written members
    | _ => none
  | _ => none

/-- Check the exact child term of one specified literal old edge. A named
child additionally needs the selected source card's actual raw row ordinal
on arrival. Ordinary aliases are found only in the independent prior. -/
def checkArrival {n : Nat} {p : FullProblem} {pos : Positions n}
    (table : Table) (next : Site p.old.state.core pos)
    (rawChild : Expr) (nextCard : ReadCard) : Option (Option SourceIndexPair478) :=
  match rawChild with
  | .variable name => do
    let (picked,row) ← readNamedCardRoot (rawAt p) table name next.query nextCard
    if picked.ordinals.raw = (pos.cells.get next.index).oldOrdinal ∧
        eqExpr row.right next.term = true then
      some (some picked.ordinals)
    else none
  | _ => if eqExpr rawChild next.term then some none else none

theorem checked_arrival_is_exact_original_source_row_or_literal_term
    {n : Nat} {p : FullProblem} {pos : Positions n}
    {table : Table} {next : Site p.old.state.core pos}
    {rawChild : Expr} {nextCard : ReadCard} {selection : Option SourceIndexPair478}
    (valid : checkArrival table next rawChild nextCard = some selection) :
    (selection = none ∧ (∀ name, rawChild ≠ .variable name) ∧ rawChild = next.term) ∨
    ∃ (name : Nat) (idx : SourceIndexPair478) (row : Equation),
      rawChild = .variable name ∧ selection = some idx ∧
      idx.raw = (pos.cells.get next.index).oldOrdinal ∧
      (rawAt p).equations[idx.raw]? = some row ∧
      table.authored[idx.author]? = some row ∧
      GeneralDeclarativeLowerKnown321.Alias (authoredView (rawAt p) table) name row.left ∧
      row.right = next.term := by
  cases rawChild
  case «variable» name =>
    unfold checkArrival at valid
    cases head : readNamedCardRoot (rawAt p) table name next.query nextCard with
    | none => simp [head,bind,Option.bind] at valid
    | some pair =>
      rcases pair with ⟨w,row⟩
      simp only [head,bind,Option.bind] at valid
      split at valid
      · rename_i checked
        have decision := Option.some.inj valid
        subst selection
        have exactRead := recorded_root_is_a_real_ordinal_read head
        exact .inr ⟨name,w.ordinals,row,rfl,rfl,checked.1,exactRead.1,exactRead.2.1,
          exactRead.2.2,(eq_expr _ _).mp checked.2⟩
      · cases valid
  all_goals
    simp only [checkArrival] at valid
    split at valid
    · rename_i accepted
      refine Or.inl ⟨(Option.some.inj valid).symm,?_,(eq_expr _ _).mp accepted⟩
      intro _ impossible
      cases impossible
    · cases valid

structure FocusedCardHop {n : Nat} {p : FullProblem} {pos : Positions n}
    (table : Table) (here : Site p.old.state.core pos) (move : StepWire)
    (card : ReadCard) (wanted : Fin n) where
  childCard : ReadCard
  selectedCard : subCard move.action card = some childCard
  originalStep : ReadStep p.old.state.core move here.pattern here.query here.term
  stepRead : readLiteralVisitStep p.old.state.core here.pattern here.query here.term move = some originalStep
  after : Site p.old.state.core pos
  siteRead : readHop here move wanted = some after
  matchingCode : originalStep.childQuery = after.query
  chosenSource : Option SourceIndexPair478
  sameRow : checkArrival table after originalStep.actualRawChild childCard = some chosenSource
  uses : List Occurrence
  typed : Read (authoredView (rawAt p) table) .actual originalStep.actualRawChild after.query uses

private def putCheck {A : Type} (o : Option A) : Option {a // o = some a} :=
  match o with | none => none | some value => some ⟨value,rfl⟩

def readFocusedCardHop {n : Nat} {p : FullProblem} {pos : Positions n} (table : Table)
    (here : Site p.old.state.core pos) (move : StepWire) (card : ReadCard) (wanted : Fin n) :
    Option (FocusedCardHop (p := p) table here move card wanted) := do
  let relevant ← putCheck (subCard move.action card)
  let step ← putCheck (readLiteralVisitStep p.old.state.core here.pattern here.query here.term move)
  let arrived ← putCheck (readHop here move wanted)
  if consistent : eqExpr step.val.childQuery arrived.val.query = true then
    let origin ← putCheck (checkArrival (p := p) table arrived.val step.val.actualRawChild relevant.val)
    let read ← putCheck (runReadCard (rawAt p) table .actual step.val.actualRawChild arrived.val.query relevant.val)
    pure ⟨relevant.val,relevant.property,step.val,step.property,arrived.val,arrived.property,
      (eq_expr _ _).mp consistent,origin.val,origin.property,read.val,runReadCard_sound read.property⟩
  else none

theorem focused_card_hop_is_actual_and_keeps_a_single_checked_occurrence
    {n : Nat} {p : FullProblem} {pos : Positions n} {table : Table} {here : Site p.old.state.core pos}
    {move : StepWire} {card : ReadCard} {next : Fin n}
    (x : FocusedCardHop (p := p) table here move card next) :
    next = x.after.index ∧ Nonempty (Hop here x.after move) ∧
    Read (authoredView (rawAt p) table) .actual x.originalStep.actualRawChild x.after.query x.uses := by
  obtain ⟨located,host⟩ := Producer479.reified_hop_keeps_the_same_old_place479 x.siteRead
  exact ⟨located,host,x.typed⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
