import Yulang.CommonRoleSettledSyntax

/-! Explicit links from the settled graph representation to the previously
proved Common bridges. Numeric identities use even tags for variants and odd
labels for records. Nominal shells retain their name/arguments and do not
claim a Common nominal-body interpretation. -/
namespace Yulang.CommonRoleSettledGraphBridge
open CommonRoleSettledSyntax CommonRoleRegularGraph CommonRoleGraphBisimulation

/-- Partial admission/lowering of repeated SAME-tag PLAIN variables. `none`
means outside this lowering fragment, not a language pending/rejected result. -/
def lowerRepeatedTag : List (Nat × Nat) → Option Pattern
  | [] => none
  | (tag, name) :: rest =>
      if rest.all (fun entry => entry.1 == tag) then
        some (.wrap (.variant tag) (.bind name (rest.map Prod.snd)))
      else none

theorem lower_repeated_same_tag (tag first : Nat) (rest : List Nat) :
    lowerRepeatedTag ((tag, first) :: rest.map (fun name => (tag, name))) =
      some (.wrap (.variant tag) (.bind first rest)) := by
  simp [lowerRepeatedTag, List.all_map, Function.comp_def]

def variantCycle (tag : Nat) : CommonRoleUnaryGraphBridge.UnaryGraph 1 := fun _ => (2 * tag, 0)
def recordCycle (label : Nat) : CommonRoleRecordGraphBridge.RecordGraph 1 := fun _ => (2 * label + 1, 0)

theorem variant_graph (tag : Nat) :
    (Ty.variantLoop tag).graph = CommonRoleUnaryGraphBridge.graph (variantCycle tag) := rfl

theorem record_graph (label : Nat) :
    (Ty.recordLoop label).graph = CommonRoleRecordGraphBridge.graph (recordCycle label) := rfl

/-- All finite observations, not a bounded executable test. -/
theorem variant_common_observations (tag depth : Nat) :
    CommonRoleUnaryGraphBridge.viewFinite
      (observe (Ty.variantLoop tag).graph (depth + 1) (Ty.variantLoop tag).root) =
    Common.observeTy depth (CommonRoleUnaryGraphBridge.common (variantCycle tag) 0) := by
  change CommonRoleUnaryGraphBridge.viewFinite
    (observe (CommonRoleUnaryGraphBridge.graph (variantCycle tag)) (depth + 1) (0 : Fin 1)) = _
  rw [CommonRoleUnaryGraphBridge.graph_observe, CommonRoleUnaryGraphBridge.common_observe]

theorem record_common_observations (label depth : Nat) :
    CommonRoleRecordGraphBridge.viewFinite
      (observe (Ty.recordLoop label).graph (depth + 1) (Ty.recordLoop label).root) =
    Common.observeTy depth (CommonRoleRecordGraphBridge.common (recordCycle label) 0) := by
  change CommonRoleRecordGraphBridge.viewFinite
    (observe (CommonRoleRecordGraphBridge.graph (recordCycle label)) (depth + 1) (0 : Fin 1)) = _
  rw [CommonRoleRecordGraphBridge.graph_observe, CommonRoleRecordGraphBridge.common_observe]

def boxedCycle (boxLabel loopLabel : Nat) : CommonRoleRecordGraphBridge.RecordGraph 2 :=
  fun node => if node = 0 then (2 * boxLabel + 1, 1) else (2 * loopLabel + 1, 1)

theorem boxed_graph (boxLabel loopLabel : Nat) :
    (Ty.wrap (.record boxLabel) (.recordLoop loopLabel)).graph =
      CommonRoleRecordGraphBridge.graph (boxedCycle boxLabel loopLabel) := by
  funext node
  have cases : node.val = 0 ∨ node.val = 1 := by have := node.isLt; change node.val < 2 at this; omega
  rcases cases with zero | one
  · have equal : node = ⟨0, by simp [Ty.nodes]⟩ := Fin.ext zero
    subst node; rfl
  · have equal : node = ⟨1, by simp [Ty.nodes]⟩ := Fin.ext one
    subst node; rfl

theorem boxed_common_observations (boxLabel loopLabel depth : Nat) :
    CommonRoleRecordGraphBridge.viewFinite
      (observe (Ty.wrap (.record boxLabel) (.recordLoop loopLabel)).graph (depth + 1)
        (Ty.wrap (.record boxLabel) (.recordLoop loopLabel)).root) =
    Common.observeTy depth (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 0) := by
  rw [boxed_graph]
  change CommonRoleRecordGraphBridge.viewFinite
    (observe (CommonRoleRecordGraphBridge.graph (boxedCycle boxLabel loopLabel)) (depth + 1) (0 : Fin 2)) = _
  rw [CommonRoleRecordGraphBridge.graph_observe, CommonRoleRecordGraphBridge.common_observe]

/-- The exact boxed regular graph used by X10/X11 has the expected recursive
Common meaning: box points to μ, and μ unfolds to its own required field. -/
theorem boxed_common_unfolds (boxLabel loopLabel : Nat) :
    Common.Equivalent (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 0)
      (Common.required (2 * boxLabel + 1)
        (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 1)) ∧
    Common.Equivalent (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 1)
      (Common.required (2 * loopLabel + 1)
        (CommonRoleRecordGraphBridge.common (boxedCycle boxLabel loopLabel) 1)) := by
  constructor
  · exact CommonRoleRecordGraphBridge.common_unfold _ 0
  · exact CommonRoleRecordGraphBridge.common_unfold _ 1

/-- The list graph retains the nominal identity; only its explicit payload
points to the anonymous regular graph. -/
theorem list_payload_graph (name label : Nat) :
    (Ty.wrap (.nominal name) (.recordLoop label)).graph
      ⟨0, by simp [Ty.nodes]⟩ = .nominal name [⟨1, by simp [Ty.nodes]⟩] ∧
    (Ty.wrap (.nominal name) (.recordLoop label)).graph
      ⟨1, by simp [Ty.nodes]⟩ = .structural (2 * label + 1) [⟨1, by simp [Ty.nodes]⟩] := by
  constructor <;> rfl

theorem named_body_opaque (name : Nat) :
    (Ty.atom (.named name)).graph (Ty.atom (.named name)).root = .nominal name [] ∧
      (Ty.atom (.named name)).regular = false := ⟨rfl, rfl⟩

end Yulang.CommonRoleSettledGraphBridge
