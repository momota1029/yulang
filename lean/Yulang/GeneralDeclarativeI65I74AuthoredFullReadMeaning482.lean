import Yulang.GeneralDeclarativeI65I74AuthoredFullRead482
import Yulang.GeneralDeclarativeI65I74SourceExposureMeaning481

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (PriorPhase TypedInput)
open ObservationAlternatives473 (Positions)
open GeneralDeclarativeInlineTrace331 (Read realize)
open InputCoordinates475 (rawAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeTermWalk322 (Occurrence Walk)
open GeneralDeclarativeWitnessOrigins350 (Attached)

theorem qualified_authored_basis_already_contains_exact_whole_source_read
    {n p gd} {pos : Positions n} {rel}
    (e : TypedInput p gd pos rel) (basis : PriorPhase)
    (prior : basis.ExactFor e) (authored : AuthoredBranch e) :
    Nonempty (Attached (rawAt p) basis.authors) ∧
    Read (authoredView (rawAt p) basis.authors) .actual
      (.variable e.head.orig.capture.lower) e.head.orig.code e.uses := by
  unfold AuthoredBranch at authored
  unfold PriorPhase.ExactFor at prior
  cases owner : e.backing with
  | source =>
    simp only [owner] at prior
    exact ⟨prior.1,prior.2.2.1⟩
  | released =>
    simp only [owner] at authored

theorem actual_qualified_authored_typed_input_has_finite_independent_read_card
    {n p gd} {pos : Positions n} {rel}
    (e : TypedInput p gd pos rel) (basis : PriorPhase)
    (prior : basis.ExactFor e) (authored : AuthoredBranch e) :
    ∃ wire, runReadCard (rawAt p) basis.authors .actual
      (.variable e.head.orig.capture.lower) e.head.orig.code wire = some e.uses := by
  obtain ⟨⟨attached⟩,read⟩ := qualified_authored_basis_already_contains_exact_whole_source_read
    e basis prior authored
  exact full_c331_authored_read_has_finite_card attached read

theorem exact_authored_card_uses_the_original_full_model_and_input_type
    {n p gd} {pos : Positions n} {rel}
    (e : TypedInput p gd pos rel) (basis : PriorPhase)
    (prior : basis.ExactFor e) (authored : AuthoredBranch e)
    (card : ReadCard) {uses : List Occurrence}
    (go : runReadCard (rawAt p) basis.authors .actual
      (.variable e.head.orig.capture.lower) e.head.orig.code card = some uses) :
    ∃ rebuilt : Expr,
      (∀ m : Model, FitsFull p.state m → eqAt m.assignment (.variable e.head.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt e.head.orig.code uses := by
  have supported := genuine_authored_reads_transport_into_same_support481
    (authored_prior_certifies_each_exposure_row481 e basis prior authored) (runReadCard_sound go)
  obtain ⟨out,value,walk⟩ := realize supported
  exact ⟨out,fun m fit => value m.assignment fit.1.1.1,walk⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
