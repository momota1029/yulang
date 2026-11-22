import Yulang.GeneralDeclarativeTaggedPatch340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedWhole340
open GeneralDeclarativeHead320 (State Equation Models environment)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeTaggedSources340 (BoundsRead)
open GeneralDeclarativeTaggedPatch340 (prepared captured patch)
open GeneralDeclarativeOpaqueConserve328 (Retains chain)
open GeneralDeclarativeStableReads329 (One names_one)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeGrowth327 (facts fits)
open GeneralDeclarativeEntailment320 (Entails conservative_append)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralCandidateInspection (plainNames)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate value)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans eqv_symm variant_congr union_congr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

def copied (a : Capture) (xs : List Nat) : List (Nat × Capture) := xs.map (fun b => (b,a))
def clone (whole : Expr) : Expr → Expr
  | .join a b => .join (clone whole a) (clone whole b)
  | _ => whole

/-- A syntactic walk gives each occurrence the same payload address.
There is deliberately no disjoint union branch matching here. -/
theorem reads (a : Capture) (p : Pattern)
    (positive : plainNames p = some used) (translated : translate c i p = some code) :
    Walk .actual (clone (.variable a.center) code) code (occurrences (copied a used)) := by
  cases p with
  | var n =>
    have same := Option.some.inj positive
    have codeEq := Option.some.inj translated
    cases same; cases codeEq
    exact .capture
  | join l r =>
    cases xl : plainNames l with
    | none => simp [plainNames,xl] at positive
    | some left =>
      cases xr : plainNames r with
      | none => simp [plainNames,xl,xr] at positive
      | some right =>
        have usedEq : left ++ right = used := by simpa [plainNames,xl,xr] using positive
        subst used
        cases cl : translate c i l with
        | none => simp [translate,cl] at translated
        | some leftCode =>
          cases cr : translate c i r with
          | none => simp [translate,cl,cr] at translated
          | some rightCode =>
            have codeEq : Expr.join leftCode rightCode = code := by simpa [translate,cl,cr] using translated
            subst code
            simpa only [clone,copied,occurrences,List.map_append] using
              Walk.join (reads a l xl cl) (reads a r xr cr)
  | app | record | variant => cases positive
termination_by sizeOf p

theorem clone_exact (root : Expr) (code : Expr) (m : Assignment) :
    Equivalent (value (environment m) .actual (clone root code)) (value (environment m) .actual root) := by
  cases code with
  | join a b =>
    exact eqv_trans (union_congr (clone_exact root a m) (clone_exact root b m))
      (GeneralDeclarativePlainCapture323.union_same _)
  | «variable» | primitive | nominal | record | variant => exact eqv_refl _
termination_by sizeOf code

abbrev fullState (s : State) (a : Capture) (tag : Nat) (low high : Expr) (keep : List Nat) (code : Expr) :=
  let base := prepared s a tag low high keep
  let cap := captured s a tag low high keep
  GeneralDeclarativeEntailment320.appendFacts base [⟨a.center,.variant tag (clone (.variable cap.center) code)⟩]

theorem existing_head {s : State} {p : Supported s done} (seen : BoundsRead p a tag low high)
    (keep : List Nat) (normal : normalize pat = .variant tag payload)
    (plain : plainNames payload = some names) (printed : translate c i payload = some code) :
    let final := fullState s a tag low high keep code
    let cap := captured s a tag low high keep
    Retains s final keep ∧ One final c i a pat (copied cap names) ∧
      ∀ x ∈ copied cap names, Bounds final x.2 := by
  let base := prepared s a tag low high keep
  let cap := captured s a tag low high keep
  let row : Equation := ⟨a.center,.variant tag (clone (.variable cap.center) code)⟩
  have stable := patch seen keep
  have follows : Entails base row := by
    intro m valid
    exact eqv_trans (semantic stable.2.2 m valid)
      (variant_congr tag (eqv_symm (clone_exact (.variable cap.center) code m)))
  have step : Retains base (GeneralDeclarativeEntailment320.appendFacts base [row]) keep := by
    refine ⟨facts _ _,?_⟩
    intro m valid
    refine ⟨m,(conservative_append (fun e h => ?_) m).mpr valid,fun _ _ => rfl⟩
    cases List.mem_singleton.mp h
    exact follows
  refine ⟨chain stable.1 step,⟨fits (chain stable.1 step).grows seen.interval,?_⟩,?_⟩
  · exact ⟨.variant tag code,.variant tag (clone (.variable cap.center) code),
      by simp [normal,translate,printed],.row (List.mem_append_right _ List.mem_cons_self),
      .variant (reads cap payload plain printed)⟩
  · intro x used
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp used
    exact fits step.grows stable.2.1

end Yulang.GeneralDeclarativeTaggedWhole340
