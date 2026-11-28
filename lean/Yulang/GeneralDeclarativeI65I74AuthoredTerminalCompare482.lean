import Yulang.GeneralDeclarativeI65I74AuthoredFullRead482
import Yulang.GeneralDeclarativeI65I74SourceExposureMeaning481
import Yulang.GeneralDeclarativeI65I74FiniteObservationCorrespondence474
import Yulang.GeneralDeclarativeI65I74FiniteCheckedObservation473

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open InputCoordinates475 (rawAt SourceIndexPair478)
open ObservationAlternatives473 (Positions oldPosition graphOf readTermAt findPosition found_position_is_literal)
open LiteralVisits473 (Checkpoint readCheck read_checkpoint_guards)
open CommonRoleGraphBisimulation (ObservationallyEqual bisimulation_observations)
open QuotientObservation471 (ReturnsUpToEquality quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation)

structure AuthoredTerminalCompare {n : Nat} (p : FullProblem) (table : Table)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (geom : Checkpoint n)
    (name : Nat) (code : Expr) (selectedCard : ReadCard) where
  author : ExposureWire
  row : Equation
  authorRoot : readNamedCardRoot (rawAt p) table name code selectedCard = some (author,row)
  lexical : Fin n
  spelled : oldPosition pos lexical = .rowPos author.ordinals.raw []
  sourceTerm : readTermAt p.old.state.core pos lexical = some row.right
  agrees : ObservationallyEqual (graphOf p.old.state.core pos) geom.which lexical
  sign : Bool
  checkedSign : readCheck p.old.state.core pos rel (.logical name) geom = some sign
  marks : List Occurrence
  typed : Read (authoredView (rawAt p) table) .actual (.variable name) code marks

private def evidenceFor {T : Type} (o : Option T) : Option {a // o = some a} :=
  match o with | none => none | some a => some ⟨a,rfl⟩

/-- The last named observation may use a different stored presentation of
the same regular type. The authored row is read by the source card; only
the sign is compared to ambient geometry. No permission to open another
constructor is returned by this terminal-only comparison. -/
def readAuthoredTerminalCompare {n : Nat} (p : FullProblem) (table : Table)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (geom : Checkpoint n)
    (name : Nat) (code : Expr) (card : ReadCard) :
    Option (AuthoredTerminalCompare p table pos rel geom name code card) := do
  let authored ← evidenceFor (readNamedCardRoot (rawAt p) table name code card)
  let index := authored.val.1.ordinals.raw
  let lexical ← evidenceFor (findPosition pos (.rowPos index []))
  let oldTerm ← evidenceFor (readTermAt p.old.state.core pos lexical.val)
  let bit ← evidenceFor (readCheck p.old.state.core pos rel (.logical name) geom)
  if check : eqExpr oldTerm.val authored.val.2.right = true ∧ (geom.which,lexical.val) ∈ rel then
    let uses ← evidenceFor (runReadCard (rawAt p) table .actual (.variable name) code card)
    have comparison := (read_checkpoint_guards bit.property).1.2.2.1
    have exactTerm := (eq_expr _ _).mp check.1
    pure ⟨authored.val.1,authored.val.2,authored.property,lexical.val,
      found_position_is_literal lexical.property,exactTerm ▸ oldTerm.property,
      fun d => bisimulation_observations _ _ comparison d _ _ check.2,
      bit.val,bit.property,uses.val,runReadCard_sound uses.property⟩
  else none

theorem distinct_old_terminal_presentation_never_changes_exact_regular_sign
    {n : Nat} {p : FullProblem} {table : Table} {pos : Positions n} {rel}
    {geom : Checkpoint n} {name : Nat} {code : Expr} {card : ReadCard}
    (x : AuthoredTerminalCompare p table pos rel geom name code card) :
    oldPosition pos geom.which = .logical name ∧
    oldPosition pos x.lexical = .rowPos x.author.ordinals.raw [] ∧
    (rawAt p).equations[x.author.ordinals.raw]? = some x.row ∧
    table.authored[x.author.ordinals.author]? = some x.row ∧
    GeneralDeclarativeLowerKnown321.Alias (authoredView (rawAt p) table) name x.row.left ∧
    (x.sign = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos) x.lexical) := by
  have checked := LiteralVisits473.checkpoint_does_not_substitute_a_place_or_change_its_bit x.checkedSign
  have old := recorded_root_is_a_real_ordinal_read x.authorRoot
  exact ⟨checked.1,x.spelled,old.1,old.2.1,old.2.2,checked.2.trans
    (quotient_nonempty_return_is_invariant_under_every_equal_regular_presentation x.agrees)⟩


theorem authored_terminal_compare_has_old_typed_meaning_in_every_same_fit
    {n : Nat} {p : FullProblem} {table : Table} {pos : Positions n} {rel}
    {geom : Checkpoint n} {name : Nat} {code : Expr} {card : ReadCard}
    {done : Nat → Prop} {support : GeneralDeclarativeOrigins321.Supported (rawAt p) done}
    (authority : ∀ row ∈ table.authored, support.derivesFrom row .source)
    (attached : GeneralDeclarativeWitnessOrigins350.Attached (rawAt p) table)
    (x : AuthoredTerminalCompare p table pos rel geom name code card) :
    ∃ rebuilt : Expr,
      (∀ m : Model, FitsFull p.state m →
        GeneralDeclarativeRepeatedActual323.eqAt m.assignment x.row.right rebuilt) ∧
      GeneralDeclarativeTermWalk322.Walk .actual rebuilt code x.marks := by
  obtain ⟨raw,_,near⟩ := recorded_root_is_a_real_ordinal_read x.authorRoot
  have alias := GeneralDeclarativeLowerKnown321.alias_mono
    (s := authoredView (rawAt p) table) (t := rawAt p) rfl attached.authored near
  obtain ⟨rebuilt,means,path⟩ := GeneralDeclarativeInlineTrace331.realize
    (genuine_authored_reads_transport_into_same_support481 authority x.typed)
  refine ⟨rebuilt,fun m fit => ?_,path⟩
  let eq := GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans
    (GeneralDeclarativeAliasMeaning321.alias_sound alias m.assignment fit.1.1.1)
    (fit.1.1.1.2 x.row (List.mem_of_getElem? raw))
  exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans
    (GeneralNominalCenteredHeadMatPatternSemantics.eqv_symm eq) (means m.assignment fit.1.1.1)


private theorem evidenceFor_some {A : Type} {o : Option A} {a : A} (hit : o = some a) :
    evidenceFor o = some ⟨a,hit⟩ := by
  subst o
  rfl

/-- A real closed old cone already checks all of its actual defined
alternatives. Thus an independently authorized old constructor row can
be located without changing the selected logical geometry coordinate. -/
theorem existing_terminal_guard_reifies_the_exact_authored_presentation
    {n : Nat} {p : FullProblem} {table : Table} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {geom : Checkpoint n} {name : Nat} {code : Expr} {card : ReadCard}
    {w : ExposureWire} {row : Equation} {bit : Bool} {uses : List Occurrence}
    (attached : GeneralDeclarativeWitnessOrigins350.Attached (rawAt p) table)
    (entry : readNamedCardRoot (rawAt p) table name code card = some (w,row))
    (typed : runReadCard (rawAt p) table .actual (.variable name) code card = some uses)
    (constructorRow : ObservationSyntax471.isDefinedAt row.left row = true)
    (readGeom : readCheck p.old.state.core pos rel (.logical name) geom = some bit) :
    ∃ x, readAuthoredTerminalCompare p table pos rel geom name code card = some x ∧
      x.author.ordinals = w.ordinals ∧ x.row = row ∧ x.sign = bit ∧ x.marks = uses := by
  obtain ⟨exactRaw,_,near⟩ := recorded_root_is_a_real_ordinal_read entry
  have link : GeneralDeclarativeLowerKnown321.Alias (rawAt p) name row.left :=
    GeneralDeclarativeLowerKnown321.alias_mono (s := authoredView (rawAt p) table) (t := rawAt p)
      rfl attached.authored near
  have guard := (read_checkpoint_guards readGeom).1
  have loc := (LiteralVisits473.checkpoint_does_not_substitute_a_place_or_change_its_bit readGeom).1
  have reach : FiniteWorklist.Path (CommonRoleRegularGraph.successors (graphOf p.old.state.core pos))
      geom.which geom.which := .nil _
  have options := guard.2.2.2.2.1 geom.which reach
  simp only [ObservationAlternatives473.checkAlternatives,loc] at options
  obtain ⟨whole,all⟩ := Bool.and_eq_true_iff.mp options
  have included := (ObservationRawAlias471.checked_class_is_exact_for_every_name whole row.left).mpr link
  have exactLength := (List.getElem?_eq_some_iff.mp exactRaw).1
  have hit := List.all_eq_true.mp all w.ordinals.raw (List.mem_range.mpr exactLength)
  have good : ObservationAlternatives473.includesOldDefinition pos rel geom.which w.ordinals.raw = true := by
    have exactRawCore : p.old.state.core.current.ordinary.equations[w.ordinals.raw]? = some row := exactRaw
    simpa [exactRawCore,included,constructorRow] using hit
  cases chosen : findPosition pos (.rowPos w.ordinals.raw []) with
  | none => simp [ObservationAlternatives473.includesOldDefinition,chosen] at good
  | some author =>
    have paired : (geom.which,author) ∈ rel := by
      simpa [ObservationAlternatives473.includesOldDefinition,chosen] using good
    have same : ObservationallyEqual (graphOf p.old.state.core pos) geom.which author :=
      fun d => bisimulation_observations _ _ guard.2.2.1 d _ _ paired
    have known := ObservationAlternatives473.proved_same_observation_cannot_replace_a_resolved_alternative_with_unknown
      _ _ _ same (guard.2.2.2.2.2 geom.which reach)
    have native : readTermAt p.old.state.core pos author = some row.right := by
      cases read : readTermAt p.old.state.core pos author with
      | none =>
        exact False.elim (known (by simp [graphOf,ObservationAlternatives473.readNodeAt,read,bind,Option.bind]))
      | some term =>
        obtain ⟨earlier,stored,exactTerm⟩ :=
          ObservationAlternatives473.old_lexical_row_root_never_guesses_its_ordinal
            (found_position_is_literal chosen) read
        have eq := Option.some.inj (stored.symm.trans exactRaw)
        subst earlier
        exact congrArg some exactTerm.symm
    let project := fun x : AuthoredTerminalCompare p table pos rel geom name code card =>
      (x.author.ordinals,x.row,x.sign,x.marks)
    have allExact : (readAuthoredTerminalCompare p table pos rel geom name code card).map project =
        some (w.ordinals,row,bit,uses) := by
      simp [readAuthoredTerminalCompare,evidenceFor_some entry,evidenceFor_some chosen,
        evidenceFor_some native,evidenceFor_some readGeom,evidenceFor_some typed,
        (eq_expr _ _).mpr rfl, paired,bind,Option.bind,pure,project]
    cases run : readAuthoredTerminalCompare p table pos rel geom name code card with
    | none => simp [run] at allExact
    | some receipt =>
      simp only [run,Option.map_some, Option.some.injEq,project,Prod.mk.injEq] at allExact
      exact ⟨receipt,rfl,allExact⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
