import Yulang.GeneralDeclarativeTaggedField340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedNamedPatch340
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeTaggedNamed340 (Source entails_read)
open GeneralDeclarativeTaggedPatch340 (extra ends before aliases prepared captured pre_retains)
open GeneralDeclarativePairNames326 (generated)
open GeneralDeclarativeOpaqueConserve328 (Retains chain variants)
open GeneralDeclarativeOpaqueVariantNames328 (known_bounds reads_center)
open GeneralDeclarativeEntailment320 (Entails model_append conservative_append)
open GeneralDeclarativeEqualities322 (Derives semantic)
open GeneralDeclarativeGrowth327 (facts fits)
open GeneralDeclarativeTaggedWhole340 (fullState copied clone clone_exact reads)
open GeneralDeclarativeStableReads329 (One)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm variant_congr)
open GeneralCandidateInspection (plainNames)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)

theorem prepare {s : State} {p : Supported s done} (bounds : Bounds s a)
    (loRead : Source (restriction p) tag (.variable a.lower) lo)
    (hiRead : Source (restriction p) tag (.variable a.upper) hi) (keep : List Nat) :
    Retains s (prepared s a tag lo hi keep) keep ∧
      Bounds (prepared s a tag lo hi keep) (captured s a tag lo hi keep) ∧
      Derives (prepared s a tag lo hi keep) (.variable a.center)
        (.variant tag (.variable (captured s a tag lo hi keep).center)) := by
  have stay := pre_retains s a lo hi keep
  have names := (generated s (extra a keep) (ends lo hi) (ends lo hi)).1
  have lower : Entails (before s a lo hi keep) ⟨a.lower,.variant tag (.variable (aliases s a lo hi keep).lower)⟩ :=
    fun m fit => eqv_trans (entails_read loRead m ((model_append m).mp fit).1)
      (variant_congr tag (eqv_symm (semantic names.1 m fit)))
  have upper : Entails (before s a lo hi keep) ⟨a.upper,.variant tag (.variable (aliases s a lo hi keep).upper)⟩ :=
    fun m fit => eqv_trans (entails_read hiRead m ((model_append m).mp fit).1)
      (variant_congr tag (eqv_symm (semantic names.2.2 m fit)))
  exact ⟨chain stay (variants (fits stay.grows bounds) lower upper keep),known_bounds ..,reads_center ..⟩

/-- The executable supported named join traversal can also feed the
existing head preparation, not merely state semantic equivalence of
some anonymous merged type. The generated ordinary rows remain separate
from provenance of the original inputs. -/
theorem checked_head {s : State} {p : Supported s done} (bounds : Bounds s a)
    (loRead : Source (restriction p) tag (.variable a.lower) lo)
    (hiRead : Source (restriction p) tag (.variable a.upper) hi)
    (keep : List Nat) (normal : normalize pat = .variant tag payload)
    (plain : plainNames payload = some names) (printed : translate c i payload = some code) :
    let final := fullState s a tag lo hi keep code
    let cap := captured s a tag lo hi keep
    Retains s final keep ∧ One final c i a pat (copied cap names) ∧
      ∀ x ∈ copied cap names, Bounds final x.2 := by
  let base := prepared s a tag lo hi keep
  let cap := captured s a tag lo hi keep
  let row : Equation := ⟨a.center,.variant tag (clone (.variable cap.center) code)⟩
  have stable := prepare bounds loRead hiRead keep
  have consequence : Entails base row :=
    fun m fit => eqv_trans (semantic stable.2.2 m fit)
      (variant_congr tag (eqv_symm (clone_exact (.variable cap.center) code m)))
  have step : Retains base (GeneralDeclarativeEntailment320.appendFacts base [row]) keep := by
    refine ⟨facts _ _,?_⟩
    intro m fit
    refine ⟨m,(conservative_append (fun e present => ?_) m).mpr fit,fun _ _ => rfl⟩
    cases List.mem_singleton.mp present
    exact consequence
  refine ⟨chain stable.1 step,⟨fits (chain stable.1 step).grows bounds,?_⟩,?_⟩
  · exact ⟨.variant tag code,.variant tag (clone (.variable cap.center) code),
      by simp [normal,translate,printed],.row (List.mem_append_right _ List.mem_cons_self),
      .variant (reads cap payload plain printed)⟩
  · intro x used
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp used
    exact fits step.grows stable.2.1

end Yulang.GeneralDeclarativeTaggedNamedPatch340
