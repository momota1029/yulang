import Yulang.GeneralDeclarativeAlternativeReplay333
import Yulang.GeneralDeclarativeNestedReplay332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeEmbedding333
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair finiteIndex)
open GeneralDeclarativeAlternativeReadComplete333 (read_plan)
open GeneralDeclarativeAlternativeCapture333 (captureAll)
open GeneralDeclarativeAlternativeHeads333 (endpoint_plan)
open GeneralDeclarativeNestedHeadList332 (captureArgs probe)
open GeneralDeclarativeNestedDecode332 (normalized_sound)
open GeneralDeclarativeNestedMaterial332 (assemble)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeAlternativeReplay333 (replay)
open GeneralNominalInspection (Interpretation)

/-- A concrete independently checked C332 computation is not just
simulated up to model equivalence: the same naming state and the same
literal occurrence spans occur as one of the new alternatives. -/
theorem capture_embedding {s : State} (original : Sources s)
    (ran : captureArgs original c i keep before xs ps = some (after,spans)) :
    Planned (fun src : Index s =>
      Eventually (fun f => (after,spans) ∈ captureAll src f c i keep before xs ps)) := by
  induction xs generalizing ps before after spans with
  | nil =>
    cases ps with
    | nil =>
      have same : (before,[]) = (after,spans) := Option.some.inj ran
      cases same
      exact Planned.pure fun _ => ⟨0,fun _ _ => List.mem_cons_self⟩
    | cons => cases ran
  | cons a as ih =>
    cases ps with
    | nil => cases ran
    | cons pat pats =>
      cases printed : translate c i (normalize pat) with
      | none => simp [captureArgs,printed] at ran
      | some code =>
        cases opened : GeneralDeclarativeNestedDecode332.normalized original c i .actual
            (.variable a.center) pat with
        | none => simp [captureArgs,printed,opened] at ran
        | some used =>
          cases initial : assemble before a keep code used with
          | none => simp [captureArgs,printed,opened,initial] at ran
          | some head =>
            obtain ⟨middle,first⟩ := head
            cases suffix : captureArgs original c i keep middle as pats with
            | none => simp [captureArgs,printed,opened,initial,suffix] at ran
            | some tail =>
              obtain ⟨last,rest⟩ := tail
              have same : (last,first++rest) = (after,spans) := by
                simpa [captureArgs,printed,opened,initial,suffix] using ran
              cases same
              obtain ⟨other,spelling,known⟩ := normalized_sound opened
              cases Option.some.inj (spelling.symm.trans printed)
              apply ((read_plan known).both (ih suffix)).map
              intro src available
              obtain ⟨bound,inhabit⟩ := eventually_pair available.1 available.2
              refine ⟨bound,fun f enough => ?_⟩
              obtain ⟨start,finish⟩ := inhabit f enough
              change _ ∈ captureAll src f c i keep before (a::as) (pat::pats)
              simp only [captureAll,printed]
              refine List.mem_flatMap.mpr ⟨⟨used,known⟩,start,?_⟩
              rw [initial]
              exact List.mem_map.mpr ⟨(after,rest),finish,rfl⟩

/-- The old positive ordinary pipeline embeds exactly for every
successful C332 computation. The returned output names, ordinary rows
and ordered demands are not renamed. The result does not assume their
receipt at any different state. -/
theorem exact_replay {s : State} (original : Sources s)
    (fit : ∀ a ∈ d.arguments, Bounds s a)
    (ran : GeneralDeclarativeNestedReplay332.replay r i d impl original source keep fallback targets =
      some (after,kids)) :
    Planned (fun src : Index s =>
      Eventually (fun f => (after,kids) ∈ replay src f r i d impl source keep fallback targets)) := by
  unfold GeneralDeclarativeNestedReplay332.replay at ran
  by_cases valid : probe original r.constructors i d.arguments impl.head = true
  · cases prepared : captureArgs original r.constructors i keep source d.arguments impl.head with
    | none => simp [valid,prepared] at ran
    | some out =>
      obtain ⟨middle,spans⟩ := out
      have output : compileBody r i d impl middle spans keep fallback targets = some (after,kids) := by
        simpa [valid,prepared] using ran
      have positive := GeneralDeclarativeNestedHeadList332.endpoint_list original fit valid
      apply ((endpoint_plan positive).both (capture_embedding original prepared)).map
      intro src next
      obtain ⟨first,works⟩ := eventually_pair next.1 next.2
      refine ⟨first,fun f enough => ?_⟩
      obtain ⟨seen,listed⟩ := works f enough
      change _ ∈ replay src f r i d impl source keep fallback targets
      unfold replay
      rw [ite_eq_left seen]
      exact List.mem_filterMap.mpr ⟨(middle,spans),listed,output⟩
  · simp [valid] at ran

end Yulang.GeneralDeclarativeAlternativeEmbedding333
