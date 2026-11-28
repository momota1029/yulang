import Yulang.GeneralDeclarativeI65I74TypedFocusHop482
import Yulang.GeneralDeclarativeI65I74AuthoredTerminalCompare482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint readCheck)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open InputCoordinates475 (rawAt)
open SourceExposure481 (authoredView notBinder)

theorem independent_named_source_child_reifies_actual_raw_and_authored_ordinals
    {s : GeneralDeclarativeHead320.State} {t : Table}
    {mode : GeneralNominalMaterialization.Mode} {name : Nat} {code : Expr} {uses}
    (attached : Attached s t) (inspect : notBinder code = true)
    (original : Read (authoredView s t) mode (.variable name) code uses) :
    ∃ card entry row,
      runReadCard s t mode (.variable name) code card = some uses ∧
      readNamedCardRoot s t name code card = some (entry,row) ∧
      s.equations[entry.ordinals.raw]? = some row ∧
      t.authored[entry.ordinals.author]? = some row ∧
      GeneralDeclarativeLowerKnown321.Alias (authoredView s t) name row.left := by
  obtain ⟨card,typed⟩ := full_c331_authored_read_has_finite_card attached original
  cases root : checkedRead s t mode (.variable name) code card with
  | none => simp [runReadCard,root] at typed
  | some result =>
    obtain ⟨entry,row,observed⟩ := nonbinder_read_on_a_name_exposes_a_root_ordinal inspect root
    obtain ⟨atRaw,prior,near⟩ := recorded_root_is_a_real_ordinal_read observed
    exact ⟨card,entry,row,typed,observed,atRaw,prior,near⟩

theorem independent_named_source_child_never_uses_a_pending_only_ordinary_equation
    {s : GeneralDeclarativeHead320.State} {t : Table} {name : Nat} {code : Expr}
    {card : ReadCard} {entry : ExposureWire} {row : Equation}
    (read : readNamedCardRoot s t name code card = some (entry,row))
    {settled : Nat → Prop} {support : Supported s settled}
    (command : ∀ x ∈ t.authored, support.derivesFrom x .source) :
    support.derivesFrom row .source :=
  command _ (List.mem_of_getElem? (recorded_root_is_a_real_ordinal_read read).2.1)

/-- A separately chosen authorized constructor row can be included into a
paired geometric checkpoint. The alternative geometry is not used to
produce the row, to reconstruct an alias, or to confer source ownership. -/
theorem checked_geometry_replays_the_exact_author_child_only_after_source_selection
    {n : Nat} {p : FullProblem} {t : Table} {pos : Positions n} {rel} {geom : Checkpoint n}
    {name : Nat} {code : Expr} {card : ReadCard} {chosen : ExposureWire} {row : Equation}
    {uses bit}
    (attached : Attached (rawAt p) t)
    (physical : readNamedCardRoot (rawAt p) t name code card = some (chosen,row))
    (typing : runReadCard (rawAt p) t .actual (.variable name) code card = some uses)
    (constructorRow : ObservationSyntax471.isDefinedAt row.left row = true)
    (signed : readCheck p.old.state.core pos rel (.logical name) geom = some bit) :
    ∃ receipt, readAuthoredTerminalCompare p t pos rel geom name code card = some receipt ∧
      receipt.author.ordinals = chosen.ordinals ∧ receipt.row = row ∧ receipt.sign = bit ∧
      receipt.marks = uses ∧
      Read (authoredView (rawAt p) t) .actual (.variable name) code receipt.marks := by
  obtain ⟨x,run,same,exact,sign,marks⟩ :=
    existing_terminal_guard_reifies_the_exact_authored_presentation attached physical typing constructorRow signed
  exact ⟨x,run,same,exact,sign,marks,x.typed⟩

open Producer479 (Site)
open InputCoordinates475 (SourceIndexPair478)

theorem independently_selected_named_row_replays_its_own_arrival_not_an_equal_ambient_row
    {n : Nat} {p : FullProblem} {pos : Positions n} {t : Table}
    {site : Site p.old.state.core pos} {name : Nat} {card : ReadCard}
    {exposure : ExposureWire} {row : Equation}
    (original : readNamedCardRoot (rawAt p) t name site.query card = some (exposure,row))
    (checkedPhysical : exposure.ordinals.raw = (pos.cells.get site.index).oldOrdinal)
    (actualBody : row.right = site.term) :
    checkArrival (p := p) t site (.variable name) card = some (some exposure.ordinals) := by
  simp [checkArrival,original,checkedPhysical,
    (GeneralDeclarativeWitnessLiteral349.eq_expr _ _).mpr actualBody,bind,Option.bind]

theorem selecting_an_equivalent_but_different_ambient_raw_ordinal_does_not_validate_the_same_author_card
    {n : Nat} {p : FullProblem} {pos : Positions n} {t : Table}
    {site : Site p.old.state.core pos} {name : Nat} {card : ReadCard}
    {exposure : ExposureWire} {row : Equation}
    (original : readNamedCardRoot (rawAt p) t name site.query card = some (exposure,row))
    (wrong : exposure.ordinals.raw ≠ (pos.cells.get site.index).oldOrdinal) :
    checkArrival (p := p) t site (.variable name) card = none := by
  simp [checkArrival,original,wrong,bind,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
