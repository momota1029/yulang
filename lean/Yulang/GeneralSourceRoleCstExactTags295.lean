import Yulang.GeneralSourceRoleCstRequiredControl295

/-! The compact dialogue groups many tags, but the exact declaration tags
used by the selected-head and associated-output handoff are not aliases. -/
namespace Yulang.GeneralSourceRoleCstExactTags295
open GeneralSourceRoleCstTree293 (Kind Tree)
open GeneralSourceRoleCstWireTags293 (kind compact kind_exact)
open GeneralSourceRoleCstWire293 (Wire Transfer)

theorem compact_role_exact (n : String) : compact n = Kind.role ↔ n = "RoleDeclaration" := by
  unfold compact
  split <;> simp_all

theorem compact_type_exact (n : String) : compact n = Kind.typeDecl ↔ n = "TypeDeclaration" := by
  unfold compact
  split <;> simp_all

theorem compact_head_exact (n : String) : compact n = Kind.head ↔ n = "TypeExpression" := by
  unfold compact
  split <;> simp_all

theorem exact_role_node {w : Wire} {cs : List Tree} (h : Transfer w (.node .role cs)) :
    ∃ inner, w = .node "RoleDeclaration" inner := by
  cases h with
  | node label kids =>
    have tag := (kind_exact ..).mp label
    rw [(compact_role_exact _).mp tag.2]
    exact ⟨_,rfl⟩

theorem exact_type_node {w : Wire} {cs : List Tree} (h : Transfer w (.node .typeDecl cs)) :
    ∃ inner, w = .node "TypeDeclaration" inner := by
  cases h with
  | node label kids =>
    have tag := (kind_exact ..).mp label
    rw [(compact_type_exact _).mp tag.2]
    exact ⟨_,rfl⟩

theorem exact_head_node {w : Wire} {cs : List Tree} (h : Transfer w (.node .head cs)) :
    ∃ inner, w = .node "TypeExpression" inner := by
  cases h with
  | node label kids =>
    have tag := (kind_exact ..).mp label
    rw [(compact_head_exact _).mp tag.2]
    exact ⟨_,rfl⟩

end Yulang.GeneralSourceRoleCstExactTags295
