import Yulang.GeneralDeclarativeI65I74SourceExposure481
import Yulang.GeneralDeclarativeI65I74G04Producer479
import Yulang.GeneralDeclarativeInlineFootprint331

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeInlineTrace331 (Read realize)
open GeneralDeclarativeInlineFootprint331 (trace)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open RetainedFull445 (FullProblem)
open InputCoordinates475 (rawAt SourceIndexPair478)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open Producer479 (PriorPhase TypedInput)

theorem genuine_authored_reads_transport_into_same_support481
    {s : GeneralDeclarativeHead320.State} {table : Table}
    {done : Nat → Prop} {support : Supported s done}
    (authority : ∀ row ∈ table.authored, support.derivesFrom row .source)
    {mode term code uses} (authored : Read (authoredView s table) mode term code uses) :
    Read (restriction support) mode term code uses := by
  obtain ⟨rows,source,readIn⟩ := trace authored
  exact readIn (restriction support) rfl
    (fun row present => from_source support (authority row (source present)))

theorem authorised_source_exposure_preserves_a_walk_in_every_original_fit481
    {p : FullProblem} {table : Table}
    {done : Nat → Prop} {support : Supported (rawAt p) done}
    (authority : ∀ row ∈ table.authored, support.derivesFrom row .source)
    {input code result : Expr} {wire : List ExposureWire}
    {reads : List (SourceIndexPair478 × Equation)} {uses}
    (checked : readExposureTrail (rawAt p) table code input wire = some (reads,result))
    (next : Read (authoredView (rawAt p) table) .actual result code uses) :
    reads.map Prod.fst = wire.map (·.ordinals) ∧
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m → eqAt m.assignment input rebuilt) ∧
      Walk .actual rebuilt code uses := by
  obtain ⟨opened,exactRead⟩ := exposure_trail_replays_the_exact_ordinal_row_sequence _ _ _ _ _ _ _ checked
  have replay := every_read_exposure_trail_precomposes_existing_authored_read opened next
  have legitimate := genuine_authored_reads_transport_into_same_support481 authority replay
  obtain ⟨term,means,walk⟩ := realize legitimate
  exact ⟨exactRead,term,fun m fit => means m.assignment fit.1.1.1,walk⟩

def AuthoredBranch {n p gd} {pos : ObservationAlternatives473.Positions n} {rel}
    (e : TypedInput p gd pos rel) : Prop :=
  match e.backing with
  | .source _ => True
  | .released .. => False

theorem authored_prior_certifies_each_exposure_row481
    {n p gd} {pos : ObservationAlternatives473.Positions n} {rel}
    (e : TypedInput p gd pos rel) (basis : PriorPhase)
    (prior : basis.ExactFor e) (authored : AuthoredBranch e) :
    ∀ row ∈ basis.authors.authored, e.support.derivesFrom row .source := by
  unfold AuthoredBranch at authored
  unfold PriorPhase.ExactFor at prior
  cases which : e.backing with
  | source =>
    simp only [which] at prior
    exact fun row inTable => (prior.2.1 row).mp inTable
  | released =>
    simp only [which] at authored

theorem already_qualified_source_event_preserves_original_fits_after_exposure481
    {n p gd} {pos : ObservationAlternatives473.Positions n} {rel}
    (e : TypedInput p gd pos rel) (basis : PriorPhase)
    (prior : basis.ExactFor e) (authored : AuthoredBranch e)
    {result : Expr} {wire : List ExposureWire} {reads : List (SourceIndexPair478 × Equation)}
    (checked : readExposureTrail (rawAt p) basis.authors e.head.orig.code
      (.variable e.head.orig.capture.lower) wire = some (reads,result))
    (next : Read (authoredView (rawAt p) basis.authors) .actual result e.head.orig.code e.uses) :
    reads.map Prod.fst = wire.map (·.ordinals) ∧
    ∃ rebuilt, (∀ m : Model, FitsFull p.state m →
      eqAt m.assignment (.variable e.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt e.head.orig.code e.uses :=
  authorised_source_exposure_preserves_a_walk_in_every_original_fit481
    (authored_prior_certifies_each_exposure_row481 e basis prior authored) checked next

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481
