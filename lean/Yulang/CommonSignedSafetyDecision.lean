import Yulang.CommonSignedSafetyRefinement

/-!
# Deciding whether a signed occurrence can reach any pure sink

The actual algorithm has two well-founded finite phases. It works fiberwise
in key and coordinate-list length, with no bound on integer weights. This is
not a decision procedure for reaching a specified target occurrence.
-/
namespace Yulang.CommonSignedSafetyDecision
open Common (Occurrence Row)
open CommonSignedFlowFamily (Graph Safe)
open CommonSignedSafetyPreimage (Fiber run_preserves)
open CommonSignedSafetyPreparation (State allowed CoversSafe PureEmpty initial prepare discover)
open CommonSignedSafetyRefinement (good removable refine)

/-- The rows interpreted by a finite candidate state, inside one fiber. -/
def stateRows (fiber : Fiber) (state : State n) : Fin n → Row :=
  fun slot occurrence => fiber.Contains occurrence ∧ allowed (state slot) occurrence = true

theorem stable_models (graph : Graph n) (fiber : Fiber) (state : State n)
    (noDiscovery : discover graph state = none) (noRemoval : removable graph state = none)
    (pure : PureEmpty graph state) : CommonSignedFlowFamily.Models graph (stateRows fiber state) := by
  constructor
  · intro edge member source target present runs
    refine ⟨run_preserves fiber edge.action source target present.1 runs, ?_⟩
    cases sourceEq : state edge.source with
    | none =>
      have absent := List.find?_eq_none.mp noDiscovery edge member
      have targetEq : state edge.target = none := by
        cases found : state edge.target with
        | none => rfl
        | some values => simp [sourceEq, found] at absent
      simp [targetEq, allowed]
    | some values =>
      have sourceMember : source ∈ values := by simpa [sourceEq, allowed] using present.2
      have candidate : (edge.source, source) ∈ CommonSignedSafetyRefinement.candidates state :=
        (CommonSignedSafetyRefinement.mem_candidates state edge.source source).mpr ⟨values, sourceEq, sourceMember⟩
      have absent := List.find?_eq_none.mp noRemoval (edge.source, source) candidate
      have accepted : good graph state edge.source source = true := by
        cases found : good graph state edge.source source <;> simp_all
      exact (CommonSignedSafetyRefinement.good_exact graph state edge.source source).mp accepted
        edge member rfl target runs
  · intro slot member occurrence present
    have empty := pure slot member
    simpa [stateRows, empty, allowed] using present.2

def settle (graph : Graph n) (fiber : Fiber) : State n :=
  refine graph (prepare graph fiber (initial graph))

theorem settle_covers (graph : Graph n) (fiber : Fiber) : CoversSafe graph fiber (settle graph fiber) := by
  apply CommonSignedSafetyRefinement.refine_invariant graph (CoversSafe graph fiber)
  · exact CommonSignedSafetyRefinement.prune_covers_safe graph fiber
  · apply CommonSignedSafetyPreparation.prepare_invariant graph fiber (CoversSafe graph fiber)
    · exact CommonSignedSafetyPreparation.advance_covers_safe graph fiber
    · exact CommonSignedSafetyPreparation.initial_covers_safe graph fiber

theorem settle_pure (graph : Graph n) (fiber : Fiber) : PureEmpty graph (settle graph fiber) := by
  apply CommonSignedSafetyRefinement.refine_invariant graph (PureEmpty graph)
  · intro state item _ empty
    exact CommonSignedSafetyRefinement.prune_pure_empty graph state item empty
  · apply CommonSignedSafetyPreparation.prepare_invariant graph fiber (PureEmpty graph)
    · exact CommonSignedSafetyPreparation.advance_pure_empty graph fiber
    · exact CommonSignedSafetyPreparation.initial_pure_empty graph

theorem settle_no_discovery (graph : Graph n) (fiber : Fiber) : discover graph (settle graph fiber) = none := by
  apply CommonSignedSafetyRefinement.refine_invariant graph (fun state => discover graph state = none)
  · exact CommonSignedSafetyRefinement.prune_no_discovery graph
  · exact CommonSignedSafetyPreparation.prepare_finished graph fiber (initial graph)

theorem settle_models (graph : Graph n) (fiber : Fiber) :
    CommonSignedFlowFamily.Models graph (stateRows fiber (settle graph fiber)) :=
  stable_models graph fiber (settle graph fiber) (settle_no_discovery graph fiber)
    (CommonSignedSafetyRefinement.refine_finished graph _) (settle_pure graph fiber)

/-- Every graph, every fiber, every original node and every occurrence in the
fiber. Neither solver success nor a semantic reachability check is a premise. -/
theorem settle_exact (graph : Graph n) (fiber : Fiber) (slot : Fin n) (occurrence : Occurrence)
    (within : fiber.Contains occurrence) :
    allowed (settle graph fiber slot) occurrence = true ↔ Safe graph slot occurrence := by
  constructor
  · intro accepted
    exact CommonSignedFlowFamily.model_seed_safe (settle_models graph fiber) slot occurrence ⟨within, accepted⟩
  · exact settle_covers graph fiber slot occurrence within

/-- Total executable safety check for arbitrary signed Common occurrences. -/
def check (graph : Graph n) (slot : Fin n) (occurrence : Occurrence) : Bool :=
  allowed (settle graph ⟨occurrence.1, occurrence.2.length⟩ slot) occurrence

theorem check_exact (graph : Graph n) (slot : Fin n) (occurrence : Occurrence) :
    check graph slot occurrence = true ↔ Safe graph slot occurrence :=
  settle_exact graph ⟨occurrence.1, occurrence.2.length⟩ slot occurrence ⟨rfl, rfl⟩
end Yulang.CommonSignedSafetyDecision
