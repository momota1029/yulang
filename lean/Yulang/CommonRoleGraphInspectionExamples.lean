import Yulang.CommonRoleGraphInspection

/-!
Concrete lower-head inspection examples for X6 and X8–X12. These check the
new raw inspection component only: they are not whole-resolver conformance
theorems, and do not update those cases' NOT-EXPRESSIBLE-YET status.
-/
namespace Yulang.CommonRoleGraphInspectionExamples

open CommonRoleRegularGraph CommonRoleGraphBisimulation CommonRoleGraphInspection

/-- `:{tick int}`; the tag and the scalar identity are both encoded as 0. -/
def tickInt : Graph 2 := fun node =>
  if node = 0 then .structural 0 [1] else .scalar 0

def tickHeads : List VisibleHead :=
  [⟨0, 0, .structural 0 [.shared [0, 1]]⟩,
   ⟨0, 1, .structural 0 [.scalar 0]⟩]

theorem merged_payload_observations :
    inspectVisible tickInt 0 0 tickHeads =
      [(0, .matched [(0, 1), (1, 1)]), (1, .matched [])] := by
  decide +kernel

/-- A list whose payload is an anonymous regular structural node. -/
def listLoop : Graph 2 := fun node =>
  if node = 0 then .nominal 0 [1] else .structural 1 [1]

theorem list_captures_loop :
    inspect listLoop (.nominal 0 [.variable 0]) 0 = .matched [(0, 1)] ∧
      regularAt listLoop 1 = true := by
  constructor <;> decide +kernel

/-- `{box: μ}` where `μ = {next: μ}`. -/
def boxedLoop : Graph 2 := fun node =>
  if node = 0 then .structural 0 [1] else .structural 1 [1]

def boxHeads : List VisibleHead :=
  [⟨0, 0, .structural 0 [.variable 0]⟩,
   ⟨0, 1, .structural 0 [.structural 1 [.variable 1]]⟩]

theorem boxed_loop_observations :
    inspectVisible boxedLoop 0 0 boxHeads =
      [(0, .matched [(0, 1)]), (1, .cycle 1)] := by
  decide +kernel

theorem boxed_loop_all_observations :
    inspectAllVisible boxedLoop 0 0 boxHeads =
      [(0, [.matched [(0, 1)]]), (1, [.cycle 1])] := by
  decide +kernel

/-- An earlier rigid mismatch does not erase a later cycle observation.
Whether that cycle belongs to an applicable candidate is a later obligation. -/
def twoFields : Graph 3 := fun node =>
  if node = 0 then .structural 0 [1, 2]
  else if node = 1 then .scalar 0 else .structural 1 [2]

theorem sibling_evidence_retained :
    inspectAll twoFields (.structural 0 [.scalar 1, .structural 1 [.variable 0]]) 0 =
      [.mismatch, .cycle 2] := by
  decide +kernel

/-- A named recursive tree is matched by its nominal name without opening
its declaration body. -/
def namedTree : Graph 1 := fun _ => .nominal 9 []

theorem named_tree_observation :
    regularAt namedTree 0 = false ∧ inspect namedTree (.nominal 9 []) 0 = .matched [] := by
  constructor <;> decide +kernel

/-- The same snapshot entry checks all five head shapes; it does not yet
generate where-children or classify completed dictionaries. -/
theorem requested_head_snapshots :
    inspectSnapshot tickInt 0 0 tickHeads =
      .heads [(0, [.matched [(0, 1), (1, 1)]]), (1, [.matched []])] ∧
    inspectSnapshot listLoop 0 0 [⟨0, 0, .nominal 0 [.variable 0]⟩] =
      .heads [(0, [.matched [(0, 1)]])] ∧
    inspectSnapshot listLoop 0 1 [⟨0, 0, .variable 0⟩] = .cycle 1 ∧
    inspectSnapshot boxedLoop 0 0 boxHeads =
      .heads [(0, [.matched [(0, 1)]]), (1, [.cycle 1])] ∧
    inspectSnapshot namedTree 0 0 [⟨0, 0, .nominal 9 []⟩] =
      .heads [(0, [])] := by
  repeat' constructor <;> decide +kernel

end Yulang.CommonRoleGraphInspectionExamples
