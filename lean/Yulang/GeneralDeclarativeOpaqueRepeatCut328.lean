import Yulang.GeneralDeclarativeOpaqueFixtureModels328
import Yulang.GeneralDeclarativeOpaqueShared328

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueRepeatCut328
open GeneralDeclarativeOpaqueFixture328 (final authorized scalar oldRows endpoints range_root leftCapture rightCapture support)
open GeneralDeclarativeOpaqueFixtureModels328 (assignment fitted hidden_equiv)
open GeneralDeclarativePairDecl326 (interpret rootArg)
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeOpaqueGroup328 (Sharing)
open GeneralDeclarativeOpaqueIntervals328 (low high)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralDeclarativeRepeat320 (int top_not_int)
open CommonNominalFullCarrier (Equivalent Ty common_pair_iff subtype_trans)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeDemand320 (Bounds)

abbrev raw : Pattern := .app 5 [.var 0,.var 0]
abbrev code := GeneralDeclarativePairCenters326.pair (.variable 0) (.variable 0)

theorem normalized : translate constructors interpret (normalize raw) = some code := rfl

theorem lower (done : Nat → Prop) :
    Trace (restriction (support done)) .lower 0 code [⟨0,.lower,3⟩,⟨0,.lower,3⟩] :=
  .primitive (args := [3,3]) (alias_refl _) (authorized done List.mem_cons_self)
    (.cons .capture (.cons .capture .nil))

theorem upper (done : Nat → Prop) :
    Trace (restriction (support done)) .upper 2 code [⟨0,.upper,4⟩,⟨0,.upper,4⟩] :=
  .primitive (args := [4,4]) (alias_refl _)
    (authorized done (show (⟨2,high endpoints⟩ : Equation) ∈ oldRows by simp [oldRows]))
    (.cons .capture (.cons .capture .nil))

theorem unequal (swap : Bool) :
    ¬Equivalent ((assignment swap) leftCapture.center).1 ((assignment swap) rightCapture.center).1 := by
  intro shared
  cases swap
  · exact top_not_int shared.1
  · exact top_not_int shared.2

theorem no_sharing : ¬ Sharing final [(0,leftCapture),(0,rightCapture)] := by
  intro shared
  exact unequal false (shared (assignment false) (fitted false) 0 leftCapture rightCapture
    List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self))

theorem no_single_center (swap : Bool) (value : Ty) :
    ¬Equivalent ((assignment swap) 1).1 (CommonNominalFullCarrier.pair value value) := by
  intro claimed
  have pairClaim := eqv_trans (eqv_symm (hidden_equiv swap)) claimed
  have first := (common_pair_iff ..).mp pairClaim.1
  have other := (common_pair_iff ..).mp pairClaim.2
  exact unequal swap ⟨subtype_trans first.1 other.2,subtype_trans first.2 other.1⟩

/-- Actual supported endpoint traces agree even on repeated keys,
but no single actual component can realize both occurrences in the
listed model. This is deliberately *not* a claim that stable Local
selects that repeated declaration. -/
theorem exact_cut (done : Nat → Prop) :
    (Bounds final rootArg ∧
    Trace (restriction (support done)) .lower 0 code [⟨0,.lower,3⟩,⟨0,.lower,3⟩] ∧
    Trace (restriction (support done)) .upper 2 code [⟨0,.upper,4⟩,⟨0,.upper,4⟩]) ∧
    ∃ m, Models final m ∧ ∀ value, ¬Equivalent (m 1).1 (CommonNominalFullCarrier.pair value value) :=
  ⟨⟨range_root,lower done,upper done⟩,⟨assignment false,fitted false,no_single_center false⟩⟩

end Yulang.GeneralDeclarativeOpaqueRepeatCut328
