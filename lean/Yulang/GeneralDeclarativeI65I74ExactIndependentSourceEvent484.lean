import Yulang.GeneralDeclarativeI65I74ExactScopedInterior483
import Yulang.GeneralDeclarativeI65I74AuthoredInteriorSafety483
import Yulang.GeneralDeclarativeI65I74ProducerSingleVisible479
import Yulang.GeneralDeclarativeI65I74G04Producer479
import Yulang.GeneralDeclarativeI65I74ScopedRouteSound480

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open ObservationAlternatives473 (Positions oldPosition)
open LiteralVisits473 (StepWire)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open InputCoordinates475 (rawAt oneCompiledStep477)

theorem exact_fixed_geometry_trail_determines_final_site_and_bit
    {s : GeneralDeclarativeI65.State} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {first left right : Site s pos} {a b : Bool} {moves next} {otherMoves otherNext}
    (one : Trail s pos rel first moves next left a)
    (other : Trail s pos rel first otherMoves otherNext right b)
    (sameMoves : moves = otherMoves) (sameNext : next = otherNext) :
    left = right ∧ a = b := by
  induction one generalizing otherMoves otherNext with
  | stop _ bitLeft =>
    cases other with
    | stop _ bitRight =>
      refine ⟨rfl,?_⟩
      cases a <;> cases b <;> simp_all
    | step hop _ _ _ => cases sameMoves
  | @step here middle final move moves next bit hop _ safe later ih =>
    cases other with
    | stop => cases sameMoves
    | @step _ second _ action after others _ hopAlt _ _ tail =>
      simp only [List.cons.injEq] at sameMoves sameNext
      have actual := exact_hop_has_a_unique_replay479 hop
      have laterAlt := exact_hop_has_a_unique_replay479 hopAlt
      rw [←sameMoves.1,←sameNext.1] at laterAlt
      have site : middle = second := Option.some.inj (actual.symm.trans laterAlt)
      exact ih (site.symm ▸ tail) sameMoves.2 sameNext.2

theorem every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event
    {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n} {rel}
    (event : TypedInput p gd pos rel) {w : RouteWire n} {out}
    (fixed : ExactSelectedRoute event w)
    (run : readRoute p gd pos rel w = some out) : out = event.report := by
  obtain ⟨head,first,finish,_,bit,single,registered,argument,firstPattern,firstQuery,firstIndex,_,_,_,_,_,_,actual,report⟩ :=
    a_checked_route_reflects_one_actual_safe_prefix_and_exact_terminal480 run
  have selectedHead : head = event.head := by
    have firstAt := PreparedDeclarations463.each_prechecked_head_position_replays gd head
    have secondAt := PreparedDeclarations463.each_prechecked_head_position_replays gd event.head
    have zeroA : head.orig.location.visibleOrdinal = 0 := by
      have actual := head.orig.actualVisible
      change (visible p.old.state.core p.old.root)[head.orig.location.visibleOrdinal]? = _ at actual
      rw [single] at actual
      cases h : head.orig.location.visibleOrdinal with
      | zero => rfl
      | succ i => simp [h] at actual
    have zeroB := exact_single_visibility_forces_the_old_filtered_index_zero479 event
    cases a : head.orig.location with
    | mk vis arg =>
      cases b : event.head.orig.location with
      | mk vis2 arg2 =>
        rw [a] at firstAt zeroA argument
        rw [b] at secondAt zeroB
        have argumentEq := argument.trans fixed.1
        rw [b] at argumentEq
        simp only at zeroA zeroB argumentEq
        subst vis; subst vis2; subst arg
        exact Option.some.inj (firstAt.symm.trans secondAt)
  have site : first = event.root := by
    have whereFrom := firstIndex.trans fixed.2.2.1
    have code := firstQuery.trans ((congrArg (fun h => h.orig.code) selectedHead).trans event.atHead.2.symm)
    have pattern := firstPattern.trans ((congrArg (fun h => h.orig.original) selectedHead).trans event.atHead.1.symm)
    have left := siteAt_replays479 first
    have right := siteAt_replays479 event.root
    rw [whereFrom,pattern,code] at left
    exact Option.some.inj (left.symm.trans right)
  have eventTrail := Trail.step event.enters event.rootGuard event.rootSafe event.visits
  have eq := exact_fixed_geometry_trail_determines_final_site_and_bit
    (site ▸ actual) eventTrail fixed.2.2.2.1 fixed.2.2.2.2
  rw [report,selectedHead,eq.1,eq.2,fixed.2.1,fixed.1]
  have original := congrArg (List.flatMap StepWire.written) fixed.2.2.2.1
  have compiled := congrArg (List.map (oneCompiledStep477 ∘ StepWire.action)) fixed.2.2.2.1
  simp only [List.flatMap_map,List.map_map,Function.comp_def,List.flatMap_cons,List.map_cons] at original compiled
  simp only [TypedInput.report,original,compiled]
  rfl

open SourceExposure481.ClosedBank
open GeneralDeclarativeHead320 (Equation)
open InputCoordinates475 (SamePhaseInputObservation478)
open QuotientObservation471 (ReturnsUpToEquality)
open ObservationAlternatives473 (graphOf)

def IsAuthoredInput {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} (e : TypedInput p gd pos rel) : Prop :=
  match e.backing with | .source _ => True | .released .. => False

theorem independent_source_event_supplies_exact_authored_support
    {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n} {rel}
    (e : TypedInput p gd pos rel) (prior : PriorPhase)
    (source : IsAuthoredInput e) (qualified : prior.ExactFor e) :
    ∀ row ∈ prior.authors.authored, e.support.derivesFrom row .source := by
  cases backing : e.backing with
  | source =>
    unfold PriorPhase.ExactFor at qualified
    rw [backing] at qualified
    exact fun row member => (qualified.2.1 row).mp member
  | released =>
    unfold IsAuthoredInput at source
    rw [backing] at source
    exact False.elim source

/-- Given exact independently anchored old event data, the scoped reader
cannot choose another source occurrence or sign. This does not claim the
event's route automatically has independently authored cards at every hop. -/
theorem scoped_signed_interior_agrees_with_the_independently_typed_original_event
    {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {basis : PriorPhase} {wire : RootedInteriorWire n}
    (event : TypedInput p gd pos rel)
    (source : IsAuthoredInput event) (valid : basis.ExactFor event)
    (origins : ExactSelectedRoute event wire.route)
    (result : RootedInteriorReceipt p gd pos rel basis wire) :
    result.report = event.report ∧
    InteriorMeaning (p := p) basis.authors result.lexical result.approach.last result.approach.finalCard
      (readPairedIndices wire.after) result.suffix.sites.path ∧
    safeAuthorPrefixes (p := p) result.lexical result.suffix.sites.path ∧
    (event.bit = true ↔ ReturnsUpToEquality (graphOf p.old.state.core pos)
      (terminalPair (p := p) result.lexical result.approach.last result.suffix.sites.path).1.index) := by
  have exactReport := every_accepted_wire_at_the_independent_event_coordinates_reports_the_same_event
    event origins result.exactReport
  have backed := independent_source_event_supplies_exact_authored_support event basis source valid
  obtain ⟨_,_,truth,signed⟩ := rooted_interior_keeps_the_original_full_report_and_old_author_typing result backed
  refine ⟨exactReport,truth,every_nonterminal_original_author_site_in_the_rooted_suffix_is_safe result,?_⟩
  rw [exactReport] at signed
  exact signed

end Yulang.GeneralDeclarativeI65.I72.Producer479
