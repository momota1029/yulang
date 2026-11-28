import Yulang.GeneralDeclarativeI65I74RootedInteriorOriginalPose483
import Yulang.GeneralDeclarativeI65I74AuthoredInteriorSafety483
import Yulang.GeneralDeclarativeI65I74ExactScopedReport482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open Producer479 (PriorPhase readRoute)
open ObservationAlternatives473 (Positions graphOf)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)
open GeneralDeclarativeOrigins321 (Supported)
open TypedRootSafety482 (AllRootSafe)
open LiteralVisits473 (Checkpoint)
open QuotientObservation471 (ReturnsUpToEquality)

/-- This entry is only for a rooted, independently authorized paired
suffix. It does not add a tag to any installed full dispatcher. -/
def checkScopedInterior483 {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase) (wire : RootedInteriorWire n)
    (report : SamePhaseInputObservation478) : Bool :=
  checkSignedRead (readRootedInterior p gd pos rel basis wire) (·.report) report

theorem exact_scoped_interior_check_replays_the_same_rooted_read
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase} {wire : RootedInteriorWire n}
    {report : SamePhaseInputObservation478} :
    checkScopedInterior483 p gd pos rel basis wire report = true ↔
      ∃ found, readRootedInterior p gd pos rel basis wire = some found ∧ found.report = report :=
  exact_checked_read_cannot_substitute_observation_or_source ..

theorem exact_scoped_interior_reports_the_original_signed_site_with_no_extra_authority
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase} {wire : RootedInteriorWire n}
    {report : SamePhaseInputObservation478} {done : Nat → Prop} {support : Supported (rawAt p) done}
    (authored : ∀ row ∈ basis.authors.authored, support.derivesFrom row .source)
    (checked : checkScopedInterior483 p gd pos rel basis wire report = true) :
    readRoute p gd pos rel wire.route = some report ∧
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (fun a => a.lower))
      (wire.approach.roots.map Checkpoint.which) ∧
    ∃ found, readRootedInterior p gd pos rel basis wire = some found ∧ found.report = report ∧
      InteriorMeaning (p := p) basis.authors found.lexical found.approach.last found.approach.finalCard
        (readPairedIndices wire.after) found.suffix.sites.path ∧
      safeAuthorPrefixes (p := p) found.lexical found.suffix.sites.path ∧
      (report.outcome.2.2.2 = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos)
        (terminalPair (p := p) found.lexical found.approach.last found.suffix.sites.path).1.index) := by
  obtain ⟨found,run,eq⟩ := exact_scoped_interior_check_replays_the_same_rooted_read.mp checked
  obtain ⟨safe,geometry,src,signed⟩ := rooted_interior_keeps_the_original_full_report_and_old_author_typing found authored
  exact ⟨eq ▸ geometry,safe,found,run,eq,src,
    every_nonterminal_original_author_site_in_the_rooted_suffix_is_safe found,eq ▸ signed⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
