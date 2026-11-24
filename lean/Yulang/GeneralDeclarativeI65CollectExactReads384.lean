import Yulang.GeneralDeclarativeI65OpenOrdinaryRead384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeGraphRows321 (shapeOf)

/-- A positive source read *before* the local premise list is made.
The generated case holds the literal emission and same-dictionary
finite producer proof; it is not the unkeyed C383 erasure. -/
inductive SourcedOrdinaryRead384 (source : ExactSelectedRule384)
    (ordinary : LogicalOutputEquation383) (tagged : ChosenTaggedBinding383)
    (direct : DirectEquation383) (s : State) : Equation → Prop where
  | text : direct s row → row ∈ s.current.ordinary.equations →
      SourcedOrdinaryRead384 source ordinary tagged direct s row
  | produced {q : Request} {d : Dictionary} {ordinal : Nat} :
      Nonempty (ExactSupport384 source ordinary tagged s (.ordinary q d ordinal row)) →
      SourcedOrdinaryRead384 source ordinary tagged direct s row

theorem collect_sourced_ordinary_read384 {source ordinary tagged direct s row}
    (read : SourcedOrdinaryRead384 source ordinary tagged direct s row) :
    ∃ needs, Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      OpenOrdinaryRead384 direct s needs row := by
  cases read with
  | text why retained => exact ⟨[],⟨.nil⟩,.text why retained⟩
  | produced exactProof =>
    obtain ⟨⟨emission,completion⟩⟩ := exactProof
    exact ⟨[_],⟨.cons emission completion .nil⟩,.output (pos := 0) rfl⟩

theorem sourced_ordinary_read_of_exact_slots384 {source ordinary tagged direct s needs row}
    (supports : ExactSupportForest384 source ordinary tagged s needs)
    (read : OpenOrdinaryRead384 direct s needs row) :
    SourcedOrdinaryRead384 source ordinary tagged direct s row := by
  cases read with
  | text why retained => exact .text why retained
  | @output pos q d ordinal atIndex =>
    exact .produced ⟨exact_support_at384 supports pos atIndex⟩

/-- Renumbering the local premise vector never alters the original
output ordinal *inside* a need. These indices are different things. -/
def NeedEmbedding384 (before after : List OutputNeed384) : Prop :=
  ∀ (i : Nat) need, before[i]? = some need → ∃ j : Nat, after[j]? = some need

theorem needs_embed_left384 (first last : List OutputNeed384) :
    NeedEmbedding384 first (first ++ last) := by
  intro i need hit
  have inLeft := List.getElem?_eq_some_iff.mp hit
  exact ⟨i,List.getElem?_append_left inLeft.1 ▸ hit⟩

theorem needs_embed_right384 (first last : List OutputNeed384) :
    NeedEmbedding384 last (first ++ last) := by
  intro i need hit
  refine ⟨first.length + i,?_⟩
  rw [List.getElem?_append_right (by omega)]
  simpa using hit

theorem reindex_open_ordinary_read384 {direct s before after row}
    (embedded : NeedEmbedding384 before after)
    (read : OpenOrdinaryRead384 direct s before row) :
    OpenOrdinaryRead384 direct s after row := by
  cases read with
  | text why retained => exact .text why retained
  | @output pos q d ordinal atIndex =>
    obtain ⟨j,found⟩ := embedded pos _ atIndex
    exact .output (pos := j) found

theorem reindex_open_alias384 {direct intervals constraints s before after a b}
    (embedded : NeedEmbedding384 before after)
    (alias : OpenAlias384 direct intervals constraints s before a b) :
    OpenAlias384 direct intervals constraints s after a b := by
  induction alias with
  | bounds l r => exact .bounds l r
  | forward e => exact .forward (reindex_open_ordinary_read384 embedded e)
  | backward e => exact .backward (reindex_open_ordinary_read384 embedded e)
  | trans _ _ a b => exact .trans a b

theorem reindex_open_observed384 {direct intervals constraints s before after slot shape}
    (embedded : NeedEmbedding384 before after)
    (seen : OpenObserved384 direct intervals constraints s before slot shape) :
    OpenObserved384 direct intervals constraints s after slot shape := by
  cases seen with
  | shape l r reads =>
    exact .shape (reindex_open_alias384 embedded l) (reindex_open_ordinary_read384 embedded r) reads

def append_exact_supports384 {source ordinary tagged s first last}
    (left : ExactSupportForest384 source ordinary tagged s first)
    (right : ExactSupportForest384 source ordinary tagged s last) :
    ExactSupportForest384 source ordinary tagged s (first ++ last) :=
  match left with
  | .nil => right
  | .cons site selected later => .cons site selected (append_exact_supports384 later right)

end Yulang.GeneralDeclarativeI65
