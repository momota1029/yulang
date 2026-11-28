import Yulang.GeneralDeclarativeI65I74ArchivedRead482
import Yulang.GeneralDeclarativeI65I74NamedTerminalRoute482

namespace Yulang.GeneralDeclarativeI65.I72.ArchiveValidation482
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions graphOf)
open Producer479 (PriorPhase readRoute)
open SourceExposure481.ClosedBank (NamedTerminalWire NamedTerminalReceipt readNamedTerminalRoute
  ReadCard original_terminal_report_with_distinct_author_is_sound)
open QuotientObservation471 (ReturnsUpToEquality)
open InputCoordinates475 (rawAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Walk)

structure ArchivedNamedRouteWire (n : Nat) where
  named : NamedTerminalWire n
  archiveCard : ReadCard

structure ArchivedNamedRouteReceipt {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase) (wire : ArchivedNamedRouteWire n) where
  exactRoute : NamedTerminalReceipt p gd pos rel basis wire.named
  archival : VerifiedArchivedTyping p basis exactRoute.original.orig.capture.lower
    exactRoute.original.orig.code exactRoute.initial.initialIndices exactRoute.initial.used

/-- The separately recorded capture is checked at the same original head,
exact initial ordinal pair and ordered Uses, even if the distinct terminal
geometry row is not in the archive. -/
def readArchivedNamedRoute {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase) (wire : ArchivedNamedRouteWire n) :
    Option (ArchivedNamedRouteReceipt p gd pos rel basis wire) := do
  let exact ← readNamedTerminalRoute p gd pos rel basis wire.named
  let archive ← readArchivedTyping p basis exact.original.orig.capture.lower exact.original.orig.code
    exact.initial.initialIndices exact.initial.used wire.archiveCard
  pure ⟨exact,archive⟩

theorem archived_named_route_keeps_the_old_terminal_and_exact_prior_capture
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {basis : PriorPhase} {wire : ArchivedNamedRouteWire n}
    {done : Nat → Prop} {support : GeneralDeclarativeOrigins321.Supported (rawAt p) done}
    (authority : ∀ row ∈ basis.authors.authored, support.derivesFrom row .source)
    (out : ArchivedNamedRouteReceipt p gd pos rel basis wire) :
    basis.recordedReads = some out.archival.archived ∧
    out.exactRoute.initial.initialIndices ∈ out.archival.archived ∧
    readRoute p gd pos rel wire.named.route = some out.exactRoute.initial.output ∧
    (out.exactRoute.initial.output.outcome.2.2.2 = true ↔
      ReturnsUpToEquality (graphOf p.old.state.core pos) out.exactRoute.conclusion.lexical) ∧
    ∃ rebuilt : Expr, (∀ m : Model, FitsFull p.state m →
      eqAt m.assignment (.variable out.exactRoute.original.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt out.exactRoute.original.orig.code out.exactRoute.initial.used := by
  have old := original_terminal_report_with_distinct_author_is_sound out.exactRoute authority
  exact ⟨out.archival.recorded,the_archived_root_reference_is_one_of_the_literally_recovered_pairs out.archival,
    old.2.1,old.2.2.2.2.1,verified_archived_typing_has_same_meaning_in_every_original_fit authority out.archival⟩

end Yulang.GeneralDeclarativeI65.I72.ArchiveValidation482
