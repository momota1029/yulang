import Yulang.GeneralDeclarativeAlternativeRange333

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeRanged333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeRead333 (read)
open GeneralDeclarativeAlternativeReadComplete333 (read_plan)
open GeneralDeclarativeAlternativeHeads333 (Centers)
open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair)
open GeneralDeclarativeAlternativeRange333 (Known materialize materialize_exact materialize_exists)
open GeneralDeclarativeGrowth327 (Extends fits trans)
open GeneralDeclarativeObserverGrowth330 (preserve sources_grow)
open GeneralDeclarativeInlineGrowth331 (extend)
open GeneralDeclarativeOpaqueConserve328 (Retains refl chain)
open GeneralDeclarativeStableReads329 (Heads One)

open GeneralDeclarativeAlternativeCapture333 (Captured transport_one)

/-- Alternative capture enumeration with independently verified old
intervals retained at their actual center. -/
def captureRanged (view : Known origin) (src : Index s) (fuel : Nat) (c : Constructors) (i : Interpretation)
    (keep : List Nat) (current : State) : List Capture → List Pattern → List Captured
  | [],[] => [(current,[])]
  | a::as,p::ps =>
    match translate c i (normalize p) with
    | none => []
    | some code =>
      (read src fuel .actual (.variable a.center) code).flatMap fun seen =>
        match materialize view current a keep code seen.val with
        | none => []
        | some (middle,uses) =>
          (captureRanged view src fuel c i keep middle as ps).map fun (out,rest) => (out,uses++rest)
  | _,_ => []

theorem capture_sound {s t : State} {p : Supported s done}
    (view : Known s) (src : Index (restriction p)) (old : Extends s t) (bounds : ∀ a ∈ xs, Bounds s a)
    (found : (out,spans) ∈ captureRanged view src depth c i keep t xs ps) :
    Retains t out keep ∧ Heads out c i xs ps spans ∧ ∀ a ∈ spans, Bounds out a.2 := by
  induction xs generalizing ps t out spans with
  | nil =>
    cases ps with
    | nil =>
      have same : (out,spans) = (t,[]) := List.mem_singleton.mp found
      cases same
      exact ⟨refl _ _,.nil,fun _ absent => False.elim (List.not_mem_nil absent)⟩
    | cons p ps => cases found
  | cons a as ih =>
    cases ps with
    | nil => cases found
    | cons pat pats =>
      cases printed : translate c i (normalize pat) with
      | none => simp [captureRanged,printed] at found
      | some code =>
        simp only [captureRanged,printed] at found
        obtain ⟨hit,_,proposed⟩ := List.mem_flatMap.mp found
        cases made : materialize view t a keep code hit.val with
        | none => simp [made] at proposed
        | some middle =>
          obtain ⟨middle,first⟩ := middle
          rw [made] at proposed
          obtain ⟨⟨last,rest⟩,arrived,same⟩ := List.mem_map.mp proposed
          cases same
          obtain ⟨kept,whereHead,good⟩ := materialize_exact view old (fits old (bounds a List.mem_cons_self)) printed
            (extend (sources_grow p old) hit.property) made
          obtain ⟨tail,tailHead,evidence⟩ := ih (trans old kept.grows)
            (fun q here => bounds q (List.mem_cons_of_mem _ here)) arrived
          refine ⟨chain kept tail,.cons (transport_one tail.grows whereHead) tailHead,?_⟩
          intro choice parent
          rcases List.mem_append.mp parent with now|later
          · exact fits tail.grows (good _ now)
          · exact evidence _ later

/-- Representative-independent existence. Starting from genuine
actual ordinary reads for a whole head list, extract one finite
packet and a sufficient depth, uniformly over all ordinary extensions
of the naming state. No precompiled Frame or choice is supplied. -/
theorem capture_plan {s : State} {p : Supported s done}
    (view : Known s) (actual : Centers p c i xs ps) (keep : List Nat) :
    Planned (fun src : Index (restriction p) =>
      Eventually (fun f => ∀ (t : State), Extends s t →
        ∃ out, out ∈ captureRanged view src f c i keep t xs ps)) := by
  induction actual with
  | nil =>
    exact Planned.pure fun _ => ⟨0,fun _ _ t _ => ⟨(t,[]),List.mem_cons_self⟩⟩
  | cons h rest ih =>
    obtain ⟨box,code,sites,printed,traced⟩ := h
    apply ((read_plan traced).both ih).map
    intro src combined
    obtain ⟨least,works⟩ := eventually_pair combined.1 combined.2
    refine ⟨least,fun f enough t reaches => ?_⟩
    obtain ⟨observe,later⟩ := works f enough
    have here := extend (sources_grow p reaches) traced
    obtain ⟨middle,spans,made⟩ := materialize_exists view (fits reaches box) printed
      (p := preserve p reaches) here
    obtain ⟨kept,_,_⟩ := materialize_exact view reaches (fits reaches box) printed
      (p := preserve p reaches) here made
    obtain ⟨⟨out,rest⟩,ready⟩ := later middle (trans reaches kept.grows)
    refine ⟨(out,spans++rest),?_⟩
    simp only [captureRanged,printed]
    refine List.mem_flatMap.mpr ⟨⟨sites,traced⟩,observe,?_⟩
    rw [made]
    exact List.mem_map.mpr ⟨(out,rest),ready,rfl⟩

end Yulang.GeneralDeclarativeAlternativeRanged333
