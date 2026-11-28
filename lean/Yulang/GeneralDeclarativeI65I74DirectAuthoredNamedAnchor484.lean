import Yulang.GeneralDeclarativeI65I74IndependentNamedLayer484
import Yulang.GeneralDeclarativeI65I74AuthoredTerminalCompare482
import Yulang.GeneralDeclarativeI65I74AuthoredInterior483

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions oldPosition graphOf readTermAt findPosition found_position_is_literal)
open LiteralVisits473 (Checkpoint readCheck read_checkpoint_guards)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)
open InputCoordinates475 (rawAt)
open SourceExposure481 (authoredView)
open CommonRoleGraphBisimulation (bisimulation_observations)

structure DirectNamedAnchor {n : Nat} (p : FullProblem) (table : Table)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (geom : Checkpoint n)
    (name : Nat) (code : Expr) (w : ExposureWire) (residual : ReadCard) where
  comparison : AuthoredTerminalCompare p table pos rel geom name code (.expose w residual)
  exactExposure : readExposure (rawAt p) table name code w = some comparison.row
  exactOrdinal : comparison.author.ordinals = w.ordinals
  after : runReadCard (rawAt p) table .actual comparison.row.right code residual = some comparison.marks

/-- This re-anchors the authorized lexical presentation. It does not
take another raw Hop and does not change the chosen ambient geometry. -/
def readDirectNamedAnchor {n : Nat} (p : FullProblem) (table : Table)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (geom : Checkpoint n)
    (name : Nat) (code : Expr) (w : ExposureWire) (residual : ReadCard) :
    Option (DirectNamedAnchor p table pos rel geom name code w residual) := do
  let named ← collectedForInterior (readExposure (rawAt p) table name code w)
  let typed ← collectedForInterior (runReadCard (rawAt p) table .actual named.val.right code residual)
  let lexical ← collectedForInterior (findPosition pos (.rowPos w.ordinals.raw []))
  let oldTerm ← collectedForInterior (readTermAt p.old.state.core pos lexical.val)
  let bit ← collectedForInterior (readCheck p.old.state.core pos rel (.logical name) geom)
  if stated : eqExpr oldTerm.val named.val.right = true ∧ (geom.which,lexical.val) ∈ rel then
    let cmp : AuthoredTerminalCompare p table pos rel geom name code (.expose w residual) :=
      ⟨w,named.val,by simp [readNamedCardRoot,named.property],lexical.val,
       found_position_is_literal lexical.property,(eq_expr _ _).mp stated.1 ▸ oldTerm.property,
       fun d => bisimulation_observations _ _ (read_checkpoint_guards bit.property).1.2.2.1 d _ _ stated.2,
       bit.val,bit.property,typed.val,
       SourceExposure481.one_source_exposure_reads_in_the_same_authored_view named.property (runReadCard_sound typed.property)⟩
    pure ⟨cmp,named.property,rfl,typed.property⟩
  else none

private theorem note_option_with_its_original_proof {A : Type} {o : Option A} {a : A}
    (same : o = some a) : collectedForInterior o = some ⟨a,same⟩ := by subst o; rfl

theorem direct_named_anchor_replays_separate_existing_components
    {n : Nat} {p : FullProblem} {table : Table} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {geom : Checkpoint n} {name : Nat} {code : Expr} {w : ExposureWire} {residual : ReadCard}
    {row : GeneralDeclarativeHead320.Equation} {uses : List Occurrence} {lexical : Fin n} {bit : Bool}
    (old : readExposure (rawAt p) table name code w = some row)
    (typed : runReadCard (rawAt p) table .actual row.right code residual = some uses)
    (actual : findPosition pos (.rowPos w.ordinals.raw []) = some lexical)
    (atLexical : readTermAt p.old.state.core pos lexical = some row.right)
    (signed : readCheck p.old.state.core pos rel (.logical name) geom = some bit)
    (pair : (geom.which,lexical) ∈ rel) :
    ∃ out, readDirectNamedAnchor p table pos rel geom name code w residual = some out ∧
      out.comparison.row = row ∧ out.comparison.lexical = lexical ∧
      out.comparison.sign = bit ∧ out.comparison.marks = uses := by
  simp [readDirectNamedAnchor,note_option_with_its_original_proof old,note_option_with_its_original_proof typed,
    note_option_with_its_original_proof actual,note_option_with_its_original_proof atLexical,
    note_option_with_its_original_proof signed,(eq_expr _ _).mpr rfl,pair,bind,Option.bind,pure]

open GeneralDeclarativeWitnessOrigins350 (Attached)
open SourceExposure481 (notBinder)
open ObservationRawAlias471 (checked_class_is_exact_for_every_name)

theorem existing_exact_named_checkpoint_includes_every_independently_selected_author_row
    {n : Nat} {p : FullProblem} {table : Table} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {geom : Checkpoint n} {name : Nat} {code : Expr} {w : ExposureWire}
    {row : GeneralDeclarativeHead320.Equation} {bit : Bool}
    (attached : Attached (rawAt p) table)
    (read : readExposure (rawAt p) table name code w = some row)
    (nonvariable : ObservationSyntax471.isDefinedAt row.left row = true)
    (checked : readCheck p.old.state.core pos rel (.logical name) geom = some bit) :
    ∃ lexical, findPosition pos (.rowPos w.ordinals.raw []) = some lexical ∧
      readTermAt p.old.state.core pos lexical = some row.right ∧ (geom.which,lexical) ∈ rel := by
  obtain ⟨raw,_,_,alias⟩ := SourceExposure481.exposure_read_reflects_literal_origin _ _ _ _ _ _ read
  have relation : GeneralDeclarativeLowerKnown321.Alias (rawAt p) name row.left :=
    GeneralDeclarativeLowerKnown321.alias_mono (s := authoredView (rawAt p) table) (t := rawAt p)
      rfl attached.authored alias
  obtain ⟨guard,exactSite,_⟩ := read_checkpoint_guards checked
  have options := guard.2.2.2.2.1 geom.which (.nil _)
  simp only [ObservationAlternatives473.checkAlternatives,exactSite] at options
  obtain ⟨whole,all⟩ := Bool.and_eq_true_iff.mp options
  have included := (checked_class_is_exact_for_every_name whole row.left).mpr relation
  have actualRange := List.mem_range.mpr (List.getElem?_eq_some_iff.mp raw).1
  have atOrdinal := List.all_eq_true.mp all w.ordinals.raw actualRange
  have needed : ObservationAlternatives473.includesOldDefinition pos rel geom.which w.ordinals.raw = true := by
    have stored : p.old.state.core.current.ordinary.equations[w.ordinals.raw]? = some row := raw
    simpa [stored,included,nonvariable] using atOrdinal
  cases selected : findPosition pos (.rowPos w.ordinals.raw []) with
  | none => simp [ObservationAlternatives473.includesOldDefinition,selected] at needed
  | some real =>
    have paired : (geom.which,real) ∈ rel := by
      simpa [ObservationAlternatives473.includesOldDefinition,selected] using needed
    have opts : CommonRoleGraphBisimulation.ObservationallyEqual (graphOf p.old.state.core pos)
        geom.which real := fun d => bisimulation_observations _ _ guard.2.2.1 d _ _ paired
    have registered := ObservationAlternatives473.proved_same_observation_cannot_replace_a_resolved_alternative_with_unknown
      _ _ _ opts (guard.2.2.2.2.2 geom.which (.nil _))
    have sameRow : readTermAt p.old.state.core pos real = some row.right := by
      cases found : readTermAt p.old.state.core pos real with
      | none =>
        exact False.elim (registered (by
          simp [graphOf,ObservationAlternatives473.readNodeAt,found,bind,Option.bind]))
      | some actual =>
        obtain ⟨previous,physical,body⟩ :=
          ObservationAlternatives473.old_lexical_row_root_never_guesses_its_ordinal
            (found_position_is_literal selected) found
        have exact := Option.some.inj (physical.symm.trans raw)
        subst previous
        exact congrArg some body.symm
    exact ⟨real,rfl,sameRow,paired⟩

/-- The finite source cut is reified from the independent original Read,
not from an ambient geometry occurrence. Holding a closed old cone is
still an explicit prerequisite. -/
theorem independent_named_read_reifies_an_exact_existing_author_anchor_without_any_raw_hop
    {p : FullProblem} {table : Table} {pos : Positions n} {rel}
    {geom : Checkpoint n} {name : Nat} {code : Expr} {uses bit}
    (attached : Attached (rawAt p) table)
    (inspect : notBinder code = true)
    (typing : Read (authoredView (rawAt p) table) .actual (.variable name) code uses)
    (checked : readCheck p.old.state.core pos rel (.logical name) geom = some bit) :
    ∃ w residual out,
      readDirectNamedAnchor p table pos rel geom name code w residual = some out ∧
      out.comparison.marks = uses ∧ out.comparison.sign = bit ∧
      oldPosition pos out.comparison.lexical = .rowPos w.ordinals.raw [] ∧
      (rawAt p).equations[w.ordinals.raw]? = some out.comparison.row ∧
      table.authored[w.ordinals.author]? = some out.comparison.row := by
  obtain ⟨row,w,residual,reading,nonvariable,stillTyped,_⟩ :=
    original_nonbinder_read_reifies_a_direct_author_row_and_the_same_independent_read attached inspect typing
  obtain ⟨pos,lookup,old,paired⟩ :=
    existing_exact_named_checkpoint_includes_every_independently_selected_author_row attached reading nonvariable checked
  obtain ⟨out,run,eq,_,sameSign,sameUses⟩ :=
    direct_named_anchor_replays_separate_existing_components reading stillTyped lookup old checked paired
  have origin := recorded_root_is_a_real_ordinal_read out.comparison.authorRoot
  rw [out.exactOrdinal] at origin
  exact ⟨w,residual,out,run,sameUses,sameSign,out.exactOrdinal ▸ out.comparison.spelled,origin.1,origin.2.1⟩

open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)

theorem direct_named_anchor_keeps_its_own_residual_in_every_original_fit
    {p : FullProblem} {t : Table} {pos : Positions n} {rel}
    {geom : Checkpoint n} {name : Nat} {code : Expr} {w : ExposureWire} {residual : ReadCard}
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (attached : Attached (rawAt p) t)
    (origin : ∀ row ∈ t.authored, support.derivesFrom row .source)
    (out : DirectNamedAnchor p t pos rel geom name code w residual) :
    oldPosition pos geom.which = .logical name ∧
    oldPosition pos out.comparison.lexical = .rowPos w.ordinals.raw [] ∧
    (rawAt p).equations[w.ordinals.raw]? = some out.comparison.row ∧
    t.authored[w.ordinals.author]? = some out.comparison.row ∧
    support.derivesFrom out.comparison.row .source ∧
    (∃ rebuilt : Expr, (∀ m : Model, FitsFull p.state m →
      eqAt m.assignment out.comparison.row.right rebuilt) ∧
      Walk .actual rebuilt code out.comparison.marks) := by
  obtain ⟨loc,source,physical,authored,_,_⟩ :=
    distinct_old_terminal_presentation_never_changes_exact_regular_sign out.comparison
  rw [out.exactOrdinal] at source physical authored
  exact ⟨loc,source,physical,authored,origin _ (List.mem_of_getElem? authored),
    authored_terminal_compare_has_old_typed_meaning_in_every_same_fit origin attached out.comparison⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
