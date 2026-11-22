import Yulang.GeneralDeclarativeOpenTraversal339
import Yulang.GeneralDeclarativeAritySource330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMixedEndpoint339
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeEndpointProbe321 (Matches)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeArityPlan330 (Shape Reads extract)
open GeneralDeclarativeWitnessHead334 (Argument)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize)

private def exactView (s : State) : Supported s (fun _ => False) :=
  ⟨fun row origin => row ∈ s.equations ∧ origin = .source,And.left⟩

private theorem restriction_exact (s : State) : restriction (exactView s) = s := by
  classical
  cases s with
  | mk normal rows =>
    unfold restriction
    congr
    apply List.filter_eq_self.mpr
    intro row present
    exact decide_eq_true ⟨.source,⟨present,rfl⟩,.source⟩

/-- Reuse the existing recognized structural leaf observer directly
over the actual restriction. A term whose syntax is known only to
an ordinary, unapproved row cannot enter through this theorem. -/
theorem trace_extract {view : State} (shape : Shape code) (lo : Trace view mode low code first)
    (hi : Trace view other upper code last) :
    ∃ plan, plan.code = code ∧ Reads view low upper plan := by
  rw [← restriction_exact view] at lo hi
  exact extract (p := exactView view) shape lo hi

theorem committed_argument {s : State} {p : Supported s done}
    (found : Matches (restriction p) c i arg pat)
    (domain : ∀ code, translate c i (normalize pat) = some code → Shape code)
    (keep) :
    ∃ after uses, Argument p c i keep s arg pat after uses := by
  obtain ⟨bounds,code,low,high,printed,lo,hi⟩ := found
  obtain ⟨plan,rendered,actual⟩ := trace_extract (domain code printed) lo hi
  exact ⟨_,_,.projected bounds (rendered ▸ printed) actual⟩

theorem from_known_code {s : State} {p : Supported s done}
    (found : Matches (restriction p) c i arg pat)
    (printed : translate c i (normalize pat) = some code)
    (shape : Shape code) (keep) :
    ∃ after uses, Argument p c i keep s arg pat after uses := by
  apply committed_argument found _ keep
  intro printedCode compared
  have same := Option.some.inj (printed.symm.trans compared)
  exact same ▸ shape

end Yulang.GeneralDeclarativeMixedEndpoint339
