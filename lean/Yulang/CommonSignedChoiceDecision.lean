import Yulang.CommonSignedChoiceRefinement

/-! Total support decision for signed row clauses with disjunctive targets.
Support means membership in some full model, rather than absence of EVERY
path to purity: a safe target may be chosen instead of an unsafe one. -/
namespace Yulang.CommonSignedChoiceDecision
open Common (Occurrence Row)
open CommonSignedChoicePreparation (Clause Graph Models Supported Covers supported_models prepare discover)
open CommonSignedChoiceRefinement (good good_exact removable refine)
open CommonSignedSafetyPreparation (State allowed)
open CommonSignedSafetyRefinement (candidates mem_candidates)
open CommonSignedSafetyPreimage (Fiber run_preserves)

def stateRows (fiber : Fiber) (state : State n) : Fin n → Row :=
  fun slot occurrence => fiber.Contains occurrence ∧ allowed (state slot) occurrence = true

theorem stable_models (graph : Graph n) (fiber : Fiber) (state : State n)
    (noDiscovery : discover graph state = none) (noRemoval : removable graph state = none) :
    Models graph (stateRows fiber state) := by
  intro clause member source target present runs
  have within := run_preserves fiber clause.action source target present.1 runs
  cases sourceEq : state clause.source with
  | none =>
    have absent := List.find?_eq_none.mp noDiscovery clause member
    have allFalse : clause.targets.all (fun slot => (state slot).isSome) = false := by
      cases found : clause.targets.all (fun slot => (state slot).isSome) <;> simp_all
    obtain ⟨slot, listed, isUnknown⟩ := List.all_eq_false.mp allFalse
    have targetEq : state slot = none := by
      cases found : state slot <;> simp_all
    exact ⟨slot, listed, within, by simp [targetEq, allowed]⟩
  | some values =>
    have sourceMember : source ∈ values := by simpa [sourceEq, allowed] using present.2
    have candidate := (mem_candidates state clause.source source).mpr ⟨values, sourceEq, sourceMember⟩
    have absent := List.find?_eq_none.mp noRemoval (clause.source, source) candidate
    have accepted : good graph state clause.source source = true := by
      cases found : good graph state clause.source source <;> simp_all
    obtain ⟨slot, listed, permitted⟩ := (good_exact graph state clause.source source).mp accepted clause member rfl target runs
    exact ⟨slot, listed, within, permitted⟩

def initial : State n := fun _ => none

def settle (graph : Graph n) (fiber : Fiber) : State n := refine graph (prepare graph fiber initial)

theorem settle_covers (graph : Graph n) (fiber : Fiber) : Covers graph fiber (settle graph fiber) := by
  apply CommonSignedChoiceRefinement.refine_invariant graph (Covers graph fiber)
  · exact CommonSignedChoiceRefinement.prune_covers graph fiber
  · apply CommonSignedChoicePreparation.prepare_invariant graph fiber (Covers graph fiber)
    · exact CommonSignedChoicePreparation.advance_covers graph fiber
    · intro slot occurrence _ _
      simp [initial, allowed]

theorem settle_no_discovery (graph : Graph n) (fiber : Fiber) : discover graph (settle graph fiber) = none := by
  apply CommonSignedChoiceRefinement.refine_invariant graph (fun state => discover graph state = none)
  · exact CommonSignedChoiceRefinement.prune_no_discovery graph
  · exact CommonSignedChoicePreparation.prepare_finished graph fiber initial

theorem settle_models (graph : Graph n) (fiber : Fiber) : Models graph (stateRows fiber (settle graph fiber)) :=
  stable_models graph fiber (settle graph fiber) (settle_no_discovery graph fiber)
    (CommonSignedChoiceRefinement.refine_finished graph _)

theorem settle_exact (graph : Graph n) (fiber : Fiber) (slot : Fin n) (occurrence : Occurrence)
    (within : fiber.Contains occurrence) :
    allowed (settle graph fiber slot) occurrence = true ↔ Supported graph slot occurrence :=
  ⟨fun accepted => ⟨stateRows fiber (settle graph fiber), settle_models graph fiber, within, accepted⟩,
    settle_covers graph fiber slot occurrence within⟩

def check (graph : Graph n) (slot : Fin n) (occurrence : Occurrence) : Bool :=
  allowed (settle graph ⟨occurrence.1, occurrence.2.length⟩ slot) occurrence

theorem check_exact (graph : Graph n) (slot : Fin n) (occurrence : Occurrence) :
    check graph slot occurrence = true ↔ Supported graph slot occurrence :=
  settle_exact graph ⟨occurrence.1, occurrence.2.length⟩ slot occurrence ⟨rfl, rfl⟩

theorem checked_successor (graph : Graph n) (clause : Clause n) (member : clause ∈ graph)
    (source target : Occurrence) (safe : check graph clause.source source = true)
    (runs : clause.action.run source = some target) :
    ∃ slot ∈ clause.targets, check graph slot target = true := by
  obtain ⟨slot, listed, supported⟩ := supported_models graph clause member source target
    ((check_exact graph clause.source source).mp safe) runs
  exact ⟨slot, listed, (check_exact graph slot target).mpr supported⟩
end Yulang.CommonSignedChoiceDecision
