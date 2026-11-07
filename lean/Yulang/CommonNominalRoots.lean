import Yulang.CommonNominalHeads

/-!
# A conservative demand order for common and nominal outer roots

This layer places invariant nominal heads alongside existing common types.
Old common types retain exactly their existing order. A nominal head has no
structural observation beyond `top`; a structural type can supply a nominal
head only when it is below `bottom`. The two clauses preserve the old
bottom/top laws without representing nominal identity by a structural tag.

The extension is at outer roots. Mixed structural constructors and recursive
graphs over these roots are not claimed here; neither is a replacement of
the existing source inference model or its solver.
-/

namespace Yulang.CommonNominalRoots

open CommonNominalHeads (Head)

inductive Ty where
  | common : Common.Ty → Ty
  | nominal : Head → Ty

inductive Demand where
  | upper : Common.Ty → Demand
  | nominal : CommonNominalHeads.Demand → Demand

def Accept : Ty → Demand → Prop
  | .common type, .upper bound => Common.Subtype type bound
  | .nominal _, .upper bound => Common.Subtype .top bound
  | .common type, .nominal _ => Common.Subtype type .bottom
  | .nominal head, .nominal demand => CommonNominalHeads.Accept head demand

def Subtype (first last : Ty) : Prop :=
  ∀ demand, Accept last demand → Accept first demand

def Equivalent (first last : Ty) : Prop := Subtype first last ∧ Subtype last first

theorem subtype_refl (type : Ty) : Subtype type type := fun _ accepted => accepted

theorem subtype_trans {first middle last : Ty}
    (before : Subtype first middle) (after : Subtype middle last) : Subtype first last :=
  fun demand accepted => before demand (after demand accepted)

/-- Preservation and reflection for every old common type, with no finite
grammar or regular-graph restriction on either endpoint. -/
theorem common_subtype_exact (first last : Common.Ty) :
    Subtype (.common first) (.common last) ↔ Common.Subtype first last := by
  constructor
  · intro below
    exact below (.upper last) (Common.subtype_refl last)
  · intro below demand accepted
    cases demand with
    | upper bound => exact Common.subtype_trans below accepted
    | nominal inner => exact Common.subtype_trans below accepted

theorem common_equivalent_exact (first last : Common.Ty) :
    Equivalent (.common first) (.common last) ↔ Common.Equivalent first last :=
  and_congr (common_subtype_exact first last) (common_subtype_exact last first)

theorem nominal_subtype_exact (first last : Head) :
    Subtype (.nominal first) (.nominal last) ↔ CommonNominalHeads.Subtype first last := by
  constructor
  · intro below demand
    exact below (.nominal demand)
  · intro below demand accepted
    cases demand with
    | upper bound => exact accepted
    | nominal inner => exact below inner accepted

theorem nominal_root_invariant_exact (first last : Head) :
    Subtype (.nominal first) (.nominal last) ↔ first.name = last.name ∧
      first.arguments.length = last.arguments.length ∧
      CommonNominalHeads.ArgumentsEquivalent first.arguments last.arguments :=
  (nominal_subtype_exact first last).trans
    (CommonNominalHeads.nominal_head_invariant_exact first last)

theorem common_nominal_exact (first : Common.Ty) (last : Head) :
    Subtype (.common first) (.nominal last) ↔ Common.Subtype first .bottom := by
  constructor
  · intro below
    exact below (.nominal (.head last.name last.arguments.length)) ⟨rfl, rfl⟩
  · intro below demand accepted
    cases demand with
    | upper bound => exact Common.subtype_trans (CommonBoundCoalescing.le_top first) accepted
    | nominal inner => exact below

private theorem top_not_below_bottom : ¬ Common.Subtype .top .bottom := by
  intro below
  let environment : CommonFinite.Environment Common.Row := ⟨fun _ => .bottom, fun _ => []⟩
  have impossible := (CommonFinite.producerLe_iff_probe _ _).mp (below 0)
    0 environment .impossible (by simp [Common.observeTy, CommonSyntax.Layer.evalAt])
  simp [Common.observeTy, CommonSyntax.Layer.evalAt, CommonFinite.ProbeAt,
    CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep] at impossible

theorem nominal_common_exact (first : Head) (last : Common.Ty) :
    Subtype (.nominal first) (.common last) ↔ Common.Subtype .top last := by
  constructor
  · intro below
    exact below (.upper last) (Common.subtype_refl last)
  · intro below demand accepted
    cases demand with
    | upper bound => exact Common.subtype_trans below accepted
    | nominal inner => exact False.elim (top_not_below_bottom (Common.subtype_trans below accepted))

theorem bottom_le (type : Ty) : Subtype (.common .bottom) type := by
  cases type with
  | common value => exact (common_subtype_exact _ _).mpr (CommonBoundCoalescing.bottom_le value)
  | nominal head => exact (common_nominal_exact _ _).mpr (Common.subtype_refl _)

theorem le_top (type : Ty) : Subtype type (.common .top) := by
  cases type with
  | common value => exact (common_subtype_exact _ _).mpr (CommonBoundCoalescing.le_top value)
  | nominal head => exact (nominal_common_exact _ _).mpr (Common.subtype_refl _)

end Yulang.CommonNominalRoots
