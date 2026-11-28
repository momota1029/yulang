import Yulang.GeneralDeclarativeI65I74InteriorCorrespondence483
import Yulang.GeneralDeclarativeI65I74TypedFocusMeaning482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (Site Hop readHop)
open LiteralVisits473 (StepWire)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeOrigins321 (Supported)
open InputCoordinates475 (rawAt)
open WrittenPattern460.PhysicalOrigin (atSource literal_occurrence)
open CommonRoleGraphBisimulation (ObservationallyEqual)
open QuotientObservation471 (ReturnsUpToEquality)

theorem paired_exact_pose_selects_the_same_subpattern
    {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {left right a b : Site s pos} {move : StepWire}
    (shared : left.pattern = right.pattern)
    (one : Hop left a move) (two : Hop right b move) :
    atSource left.pattern move.written = some a.pattern ∧ a.pattern = b.pattern := by
  have writtenOne := (literal_occurrence one.typed.writtenFrom).trans (congrArg some one.written)
  have writtenTwo := (literal_occurrence two.typed.writtenFrom).trans (congrArg some two.written)
  rw [←shared,writtenOne] at writtenTwo
  exact ⟨writtenOne,Option.some.inj writtenTwo⟩

/-- Author data and geometry are checkedForPairedFocus separately at the same written
selector. No read from the geometry side becomes authored evidence. -/
structure PairedFocusedHop {p : FullProblem} {pos : Positions n}
    (table : Table) (left right : Site p.old.state.core pos)
    (move : StepWire) (card : ReadCard) (l r : Fin n) where
  author : FocusedCardHop (p := p) table left move card l
  ambient : Site p.old.state.core pos
  ambientRead : readHop right move r = some ambient
  original : left.pattern = right.pattern
  code : left.query = right.query

def checkedForPairedFocus {A : Type} (x : Option A) : Option {y // x = some y} :=
  match x with | none => none | some y => some ⟨y,rfl⟩

def readPairedFocusedHop {p : FullProblem} {pos : Positions n} (table : Table)
    (left right : Site p.old.state.core pos) (move : StepWire) (card : ReadCard)
    (l r : Fin n) : Option (PairedFocusedHop (p := p) table left right move card l r) := do
  if same : left.pattern = right.pattern then
    if code : GeneralDeclarativeWitnessLiteral349.eqExpr left.query right.query = true then
      let authored ← readFocusedCardHop (p := p) table left move card l
      let ambient ← checkedForPairedFocus (readHop right move r)
      some ⟨authored,ambient.val,ambient.property,same,(GeneralDeclarativeWitnessLiteral349.eq_expr ..).mp code⟩
    else none
  else none

theorem paired_focused_hop_keeps_exact_pose_geometry_and_authored_meaning
    {p : FullProblem} {pos : Positions n} {table : Table}
    {left right : Site p.old.state.core pos} {move : StepWire} {card : ReadCard} {l r : Fin n}
    (visit : PairedFocusedHop (p := p) table left right move card l r)
    (positions : (List.ofFn (oldPosition pos)).Nodup)
    (leftKnown : graphOf p.old.state.core pos left.index ≠ .unresolved)
    (rightKnown : graphOf p.old.state.core pos right.index ≠ .unresolved)
    (same : ObservationallyEqual (graphOf p.old.state.core pos) left.index right.index)
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (attached : Attached (rawAt p) table)
    (authored : ∀ row ∈ table.authored, support.derivesFrom row .source) :
    l = visit.author.after.index ∧ r = visit.ambient.index ∧
    atSource left.pattern move.written = some visit.author.after.pattern ∧
    visit.author.after.pattern = visit.ambient.pattern ∧
    (ReturnsUpToEquality (graphOf p.old.state.core pos) visit.author.after.index ↔
      ReturnsUpToEquality (graphOf p.old.state.core pos) visit.ambient.index) ∧
    ∃ rebuilt : Expr,
      (∀ m : Model, FitsFull p.state m → eqAt m.assignment visit.author.after.term rebuilt) ∧
      Walk .actual rebuilt visit.author.after.query visit.author.uses := by
  obtain ⟨leftIndex,⟨one⟩,_⟩ :=
    focused_card_hop_is_actual_and_keeps_a_single_checked_occurrence visit.author
  obtain ⟨rightIndex,⟨two⟩⟩ := Producer479.reified_hop_keeps_the_same_old_place479 visit.ambientRead
  have pose := paired_exact_pose_selects_the_same_subpattern visit.original one two
  have observations := InteriorCorrespondence483.paired_selected_children_have_equal_regular_observations
    positions leftKnown rightKnown same one two rfl
  exact ⟨leftIndex,rightIndex,pose.1,pose.2,
    QuotientObservation471.quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation observations,
    scoped_selected_arrival_uses_same_original_fits_and_compiled_child attached authored visit.author⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
