import Yulang.GeneralDeclarativeI65I74StableSourceProtocol461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open Checker408 (Problem)
open WrittenPattern460

theorem actual_source_anchor_is_determined_by_its_positions_in_same_problem
    {p : Problem} {a b : OriginalAnchor p} (pos : a.location = b.location) : a = b := by
  have one := every_independent_anchor_replays a
  have two := every_independent_anchor_replays b
  rw [pos] at one
  exact Option.some.inj (one.symm.trans two)

theorem same_eligible_original_anchor_keeps_all_start_data {p : Problem}
    {a b : EligibleStart p} (eq : a.anchor = b.anchor) : a = b := by
  cases a
  cases b
  unfold EligibleStart.anchor at eq
  injection eq with sameDecl sameHead sameClause sameArg sameCode
  subst_vars
  rfl

private theorem actual_occurrence_stable_at_its_old_header {p : Problem} (a : EligibleStart p) :
    GeneralDeclarationPatterns.StableSmaller a.anchor.declaration.head a.anchor.clause.arguments := by
  exact (a.ready.descent a.clause (by rw [a.originalWhere]; exact List.mem_cons_self)).2

def priorStableAuthority {p : Problem} (h : OriginalHeaderProtocol p) (a : OriginalAnchor p) : Prop :=
  ∃ old : EligibleStart p, actualHeaderAuthority h old ∧ old.anchor = a

def priorVerifyStable {p : Problem} (h : OriginalHeaderProtocol p) (a : OriginalAnchor p) (key : Nat) : Bool :=
  ((readActualHeader h key).map (fun old => decide (old.anchor.location = a.location))).getD false

theorem prior_replays_same_original_stable_authority {p : Problem}
    (h : OriginalHeaderProtocol p) (a : OriginalAnchor p) :
    (∃ key, priorVerifyStable h a key = true) ↔ priorStableAuthority h a := by
  constructor
  · rintro ⟨k,ok⟩
    cases see : readActualHeader h k with
    | none => simp [priorVerifyStable,see] at ok
    | some old =>
      have same : old.anchor.location = a.location := by simpa [priorVerifyStable,see] using ok
      exact ⟨old,(genuine_independent_start_iff_finite_header_ticket h old).mp ⟨k,see⟩,
        actual_source_anchor_is_determined_by_its_positions_in_same_problem same⟩
  · rintro ⟨old,auth,rfl⟩
    obtain ⟨k,see⟩ := (genuine_independent_start_iff_finite_header_ticket h old).mpr auth
    exact ⟨k,by simp [priorVerifyStable,see]⟩

def previousStabilityProtocol {p : Problem} (h : OriginalHeaderProtocol p) : StableSourceProtocol p where
  Certificate := Nat
  supports := priorStableAuthority h
  stability := fun _ ⟨old,_,same⟩ => same ▸ actual_occurrence_stable_at_its_old_header old
  verifies := priorVerifyStable h
  exact := prior_replays_same_original_stable_authority h

def CoversActualProducer {p : Problem} (h : OriginalHeaderProtocol p) : Prop :=
  ∀ d (e : h.Header d), DeclarationCovered p.state.core.current.environment (h.toStart d e).declaration

theorem previousReadyCovers (p : Problem) : CoversActualProducer (alreadyReady p) :=
  fun _ h => h.preserved.covered

theorem previousHomogeneousCovers (p : Problem) : CoversActualProducer (alreadyHomogeneous p) :=
  fun _ h => h.preserved.cover

/-- On every key the modular decomposition reads the identical source data
as the existing producer, including all failures. In this instance the
stability check delegates to the real earlier author, not to syntax. -/
theorem each_previous_header_read_factors_through_same_stable_shell {p : Problem}
    (h : OriginalHeaderProtocol p) (known : CoversActualProducer h) (key : Nat) :
    readStableShell (previousStabilityProtocol h) ⟨⟨0,0,0⟩,key⟩ = readActualHeader h key := by
  cases read : readActualHeader h key with
  | none =>
    cases shell : readFiniteSourceShell p ⟨0,0,0⟩ <;>
      simp [readStableShell,shell,previousStabilityProtocol,priorVerifyStable,read,Option.bind]
  | some old =>
    have cov : DeclarationCovered p.state.core.current.environment old.declaration := by
      obtain ⟨d,e,eq⟩ :=
        (genuine_independent_start_iff_finite_header_ticket h old).mp ⟨key,read⟩
      rw [← eq]
      exact known d e
    have g := genuine_original_eligible_shell_with_source_coverage old cov
    have sh := actual_finite_shell_replays_without_any_stability_claim old.anchor g
    have prior : (previousStabilityProtocol h).verifies old.anchor key = true := by
      simp [previousStabilityProtocol,priorVerifyStable,read]
    have eq : ∀ e, joinActualStable g e = old := fun e =>
      same_eligible_original_anchor_keeps_all_start_data
        (with_stability_shell_keeps_exact_original_anchor g e)
    change readFiniteSourceShell p ⟨0,0,0⟩ = _ at sh
    simp [readStableShell,sh,prior,Option.bind,eq]

def sameEarlierDataWithExplicitShell {p : Problem} {h : OriginalHeaderProtocol p}
    (w : EligibleWire (exactHeaderReader h)) : EligibleWire (shellReadyReader (previousStabilityProtocol h)) :=
  ⟨⟨⟨0,0,0⟩,w.start⟩,w.along⟩

theorem every_previous_eligible_field_read_is_exact_after_source_separation
    {p : Problem} (h : OriginalHeaderProtocol p) (known : CoversActualProducer h)
    (w : EligibleWire (exactHeaderReader h)) :
    readEligibleField (shellReadyReader (previousStabilityProtocol h)) (sameEarlierDataWithExplicitShell w) =
      readEligibleField (exactHeaderReader h) w := by
  simp only [readEligibleField,sameEarlierDataWithExplicitShell,shellReadyReader,exactHeaderReader,
    each_previous_header_read_factors_through_same_stable_shell h known]

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
