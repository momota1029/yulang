import Yulang.B4TargetV3Totality
import Yulang.B4TargetV2Functionality

/-!
# I-19 positive regression and a distinct abstract-totality obstruction

These are schema regressions, not new fragment classifiers. All states are
stable in the fixtures, so final stability does not repair the old missing case
or supply determinism of an arbitrary Survivor relation.
-/
namespace Yulang.B4TargetV3TotalityRegressions
open CommonRoleOutermostResolver
open B4TargetV3

def vocabulary : B4Target.Vocabulary where
  Registry := Unit
  State := Unit
  Demand := Unit
  Model := Unit

/-- No candidates have yet survived an unfinished inspection of a known root. -/
def inspecting : B4Target.SourceBoundary vocabulary where
  Checked := fun _ => True
  Models := fun _ _ => True
  Step := fun _ _ _ _ => False
  Stable := fun _ _ _ => True
  Generated := fun _ _ _ _ => False
  RootPending := fun _ _ _ => False
  RootK2 := fun _ _ _ => False
  CandidateK2 := fun _ _ _ => False
  InspectionPending := fun _ _ _ => True
  Survivor := fun _ _ _ _ _ => False
  Evidence := fun _ _ _ _ _ => False
  Reorders := Eq
  DictionaryEquivalent := Eq

theorem inspecting_stable : inspecting.Stable () () () := True.intro

theorem inspecting_classify (out : Result) :
    B4TargetV3.Classify inspecting () () () out ↔ out = .pending :=
  inspection_pending_only (by simp [inspecting]) True.intro
    (by simp [inspecting]) (by simp [inspecting]) out

theorem inspecting_tree (tree : Tree) :
    Resolves (Local inspecting () ()) () tree ↔ tree = .pending :=
  inspection_pending_tree_only (by simp [inspecting]) True.intro
    (by simp [inspecting]) (by simp [inspecting]) tree

theorem inspecting_not_rejected : ¬ RejectReason inspecting () () () :=
  inspection_not_rejected True.intro (by simp [inspecting]) (by simp [inspecting])

/-- The old rule rejects unfinished inspection merely because survivors are empty. -/
theorem old_inspecting_rejected : B4TargetV2.Local inspecting () () () .rejected :=
  .rejected ⟨(by simp [inspecting]), .inr (.inr (by simp [inspecting]))⟩

theorem inspecting_total : ∃ frontier, Local inspecting () () () frontier :=
  local_total (by intro key first last h; exact False.elim h)

/-- Two root flags are changed without changing the ongoing inspection. -/
def rootK2Inspecting : B4Target.SourceBoundary vocabulary :=
  { inspecting with RootK2 := fun _ _ _ => True }

def candidateK2Inspecting : B4Target.SourceBoundary vocabulary :=
  { inspecting with CandidateK2 := fun _ _ _ => True }

theorem rootK2_inspecting_rejected : Local rootK2Inspecting () () () .rejected :=
  rootK2_rejects (by simp [rootK2Inspecting, inspecting]) True.intro

theorem candidateK2_inspecting_rejected : Local candidateK2Inspecting () () () .rejected :=
  candidateK2_rejects (by simp [candidateK2Inspecting, inspecting]) True.intro

/-- Deliberately incoherent abstract relation, not an implementation of Yulang. -/
def conflicting : B4Target.SourceBoundary vocabulary :=
  { inspecting with InspectionPending := fun _ _ _ => False
                    Survivor := fun _ _ _ key _ => key = 0 }

theorem conflicting_stable : conflicting.Stable () () () := True.intro

theorem conflicting_not_coherent : ¬ SurvivorChildrenFunctional conflicting () () () := by
  intro coherent
  have bad := coherent 0 [] [()] rfl rfl
  cases bad

/-- Same key, unequal children: neither Unique nor distinct-key ambiguity applies.
No amount of excluded-middle reasoning can manufacture a fifth Local case. -/
theorem conflicting_no_local (frontier : Frontier vocabulary.Demand) :
    ¬ Local conflicting () () () frontier := by
  intro derived
  cases derived with
  | pending h => exact h
  | inspectionPending _ h _ _ => exact h
  | rejected h =>
      rcases h.2 with root | candidate | empty
      · exact root
      · exact candidate
      · exact empty.2 0 [] rfl
  | ambiguous _ first last distinct =>
      exact distinct (first.trans last.symm)
  | selected _ unique =>
      have a := (unique.2 0 [] rfl).2
      have z := (unique.2 0 [()] rfl).2
      have bad : ([] : List Unit) = [()] := a.trans z.symm
      cases bad

/-- Formal counterexample to the requested unconditional schema totality. -/
theorem unconditional_totality_false :
    ¬ (∀ frontierBoundary : B4Target.SourceBoundary vocabulary,
      ∃ frontier, Local frontierBoundary () () () frontier) := by
  intro total
  obtain ⟨frontier, localRule⟩ := total conflicting
  exact conflicting_no_local frontier localRule

end Yulang.B4TargetV3TotalityRegressions

namespace Yulang.B4TargetV3TotalityRegressions
open CommonRoleOutermostResolver B4TargetV3

/-- The precise I-19 hole: inspection is unfinished, but a survivor already exists. -/
def nonemptyInspecting : B4Target.SourceBoundary vocabulary :=
  { inspecting with Survivor := fun _ _ _ key children => key = 0 ∧ children = [] }

theorem nonempty_inspecting_stable : nonemptyInspecting.Stable () () () := True.intro

/-- V2 has no Local derivation here, even in a stable snapshot. -/
theorem old_nonempty_inspection_hole (frontier : Frontier vocabulary.Demand) :
    ¬ B4TargetV2.Local nonemptyInspecting () () () frontier := by
  intro given
  cases given with
  | pending h => exact h
  | rejected h =>
      rcases h.2 with root | candidate | empty
      · exact root
      · exact candidate
      · exact empty 0 [] ⟨rfl, rfl⟩
  | ambiguous safe _ _ _ => exact safe.2.2.2 True.intro
  | selected safe _ => exact safe.2.2.2 True.intro

theorem nonempty_inspection_closed (tree : Tree) :
    Resolves (Local nonemptyInspecting () ()) () tree ↔ tree = .pending :=
  inspection_pending_tree_only (by simp [nonemptyInspecting, inspecting]) True.intro
    (by simp [nonemptyInspecting, inspecting]) (by simp [nonemptyInspecting, inspecting]) tree

/-- After inspection completes, no surviving candidate is genuinely a rejection. -/
def inspectedEmpty : B4Target.SourceBoundary vocabulary :=
  { inspecting with InspectionPending := fun _ _ _ => False }

theorem inspected_empty_rejected : Local inspectedEmpty () () () .rejected :=
  .rejected ⟨(by simp [inspectedEmpty, inspecting]),
    .inr (.inr ⟨(by simp [inspectedEmpty]), (by simp [inspectedEmpty, inspecting])⟩)⟩

end Yulang.B4TargetV3TotalityRegressions
