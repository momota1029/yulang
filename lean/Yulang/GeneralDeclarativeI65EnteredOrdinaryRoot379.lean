import Yulang.GeneralDeclarativeI65ActualUnaryDispatch379
import Yulang.GeneralDeclarativeI65ReturnRankCore370

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessNominalSource359 (Route SlotRead)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralDeclarativeWitnessNativeNestedMatch361 (read)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeInspect321 (Inspects Visit PatternK2 no_descendant_visit_for_nominal_capture)
open GeneralDeclarativeGraphRows321 (observed structural pending_nominal_self_cycle)
open GeneralDeclarativeK2Alias321 (AliasCycle cycle_in_alias_graph)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Supported Backed backed_iff pending_only restriction)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Declaration)

abbrev ReleaseBacked (s : State) (o : Origin) : Prop :=
  Nonempty (CurrentReleasedOrigin s o)

/-- Conditional handoff of an actual unary branch to the ordinary
graph. The lower original and exact released row are already known;
the translated query is the literal source child, not a guessed
ordinary name from equality. This supplies the first ordinary site
without claiming that the original matcher performs its K2 check. -/
structure EnteredOrdinaryRoot {s : State} {q : Request} {row : Declaration}
    (pre : NativeHeadPrefix s q row (ReleaseBacked s) .lower) where
  released : CurrentReleasedOrigin s pre.atBound.original
  sourceRoute : Route
  step : UnaryDispatch s.current.environment sourceRoute released.exactWrite.code (normalize pre.pattern)
  entered : dispatchUnary s.current.environment sourceRoute released.exactWrite.code (normalize pre.pattern) = some step
  logical : Nat
  literal : step.fromCode = .leaf logical
  query : Expr
  translated : translate (authoredRegistry s.current).constructors
    (interpretation s.current.environment.source.snapshot) step.fromPattern = some query
  inspecting : Inspects query

theorem entered_ordinary_source_root_is_current {s : State} {q : Request} {row : Declaration}
    {pre : NativeHeadPrefix s q row (ReleaseBacked s) .lower}
    (entry : EnteredOrdinaryRoot pre) :
    pre.arguments[0]? = some (.inl (.point (.ordinary (.var entry.logical)))) ∧
      Visit (structural s.current.ordinary) entry.logical entry.query entry.logical := by
  have anchored := (authored_prefix_and_unary_dispatch_agree pre entry.released entry.step).2.2
  rw [entry.literal] at anchored
  exact ⟨anchored,.here entry.inspecting⟩

theorem entered_ordinary_root_detects_cycle {s : State} {q : Request} {row : Declaration}
    {pre : NativeHeadPrefix s q row (ReleaseBacked s) .lower}
    (entry : EnteredOrdinaryRoot pre)
    (cycle : AliasCycle s.current.ordinary (observed s.current.ordinary) entry.logical) :
    PatternK2 s.current.ordinary entry.logical entry.query :=
  ⟨entry.logical,(entered_ordinary_source_root_is_current entry).2,cycle⟩

theorem entered_ordinary_root_keeps_pending_equations_for_k2
    {s : State} {q : Request} {row : Declaration}
    {pre : NativeHeadPrefix s q row (ReleaseBacked s) .lower}
    (entry : EnteredOrdinaryRoot pre) {done : Nat → Prop}
    (support : Supported s.current.ordinary done) (tag owner : Nat)
    (derived : support.derivesFrom
      (⟨entry.logical,.nominal tag [.variable entry.logical]⟩ : Equation) (.output owner))
    (onlyPending : ∀ o, support.derivesFrom
      (⟨entry.logical,.nominal tag [.variable entry.logical]⟩ : Equation) o →
        ∃ i,o = .output i ∧ ¬done i) :
    (⟨entry.logical,.nominal tag [.variable entry.logical]⟩ : Equation) ∉
        (restriction support).equations ∧
      PatternK2 s.current.ordinary entry.logical entry.query :=
  ⟨pending_only support _ onlyPending,entered_ordinary_root_detects_cycle entry
    (cycle_in_alias_graph (pending_nominal_self_cycle support owner derived))⟩

/-- In this actual nominal-with-bare-capture query there are no later
ordinary sites. This does not eliminate descendants of other shapes. -/
theorem entered_ordinary_nominal_capture_exact_rank
    {s : State} {q : Request} {row : Declaration}
    {pre : NativeHeadPrefix s q row (ReleaseBacked s) .lower}
    (entry : EnteredOrdinaryRoot pre) {tag binder : Nat}
    (shape : entry.query = .nominal tag [.variable binder]) :
    (∃ rank,SiteReturnRank s.current.ordinary entry.logical rank) ↔
      ¬PatternK2 s.current.ordinary entry.logical entry.query := by
  constructor
  · intro rank
    have safe := (local_return_rank_iff_no_cycle s.current.ordinary entry.logical).mp rank
    rw [shape]
    exact no_descendant_visit_for_nominal_capture safe
  · intro safe
    apply (local_return_rank_iff_no_cycle s.current.ordinary entry.logical).mpr
    exact fun cycle => safe (entered_ordinary_root_detects_cycle entry cycle)

end Yulang.GeneralDeclarativeI65
