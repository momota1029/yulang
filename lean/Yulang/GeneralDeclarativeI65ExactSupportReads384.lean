import Yulang.GeneralDeclarativeI65ExactDependencies384

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (AuthoredNominal Seen)

theorem ordinary_exact_support_details384
    {source ordinary tagged s q d ordinal row}
    (supported : ExactSupport384 source ordinary tagged s (.ordinary q d ordinal row)) :
    Nonempty (ExactSelected384 source ordinary tagged s q d) ∧
      Nonempty (LogicalOutputLink383 ordinary s q d ordinal row) ∧
      row ∈ s.current.ordinary.equations := by
  obtain ⟨emitted,proved⟩ := supported
  cases emitted with
  | ordinary linked live => exact ⟨⟨proved⟩,⟨linked⟩,live⟩

theorem tagged_exact_support_details384
    {source ordinary tagged s q d ordinal row}
    (supported : ExactSupport384 source ordinary tagged s (.tagged q d ordinal row)) :
    Nonempty (ExactSelected384 source ordinary tagged s q d) ∧
      LogicalTaggedUnaryOutput383 tagged s q d ordinal row ∧ row ∈ s.current.visible := by
  obtain ⟨emitted,proved⟩ := supported
  cases emitted with
  | tagged linked live => exact ⟨⟨proved⟩,linked,live⟩

theorem read_exact_ordinary_index384
    {source ordinary tagged s needs q d ordinal row} {direct : DirectEquation383}
    (support : ExactSupportForest384 source ordinary tagged s needs)
    (pos : Nat) (atIndex : needs[pos]? = some (.ordinary q d ordinal row)) :
    Nonempty (SourceEquationRead383 (ForgetExactRule384 source) direct ordinary s row) ∧
    Nonempty (ExactSelected384 source ordinary tagged s q d) ∧
    Nonempty (LogicalOutputLink383 ordinary s q d ordinal row) := by
  obtain ⟨⟨proof⟩,⟨linked⟩,live⟩ :=
    ordinary_exact_support_details384 (exact_support_at384 support pos atIndex)
  exact ⟨⟨.output q d ordinal (erase_exact_selected384 proof) linked live⟩,⟨proof⟩,⟨linked⟩⟩

theorem read_exact_tagged_index384
    {source ordinary tagged s needs q d ordinal row} {direct : DirectNominal383}
    (support : ExactSupportForest384 source ordinary tagged s needs)
    (pos : Nat) (atIndex : needs[pos]? = some (.tagged q d ordinal row)) :
    Nonempty (TaggedNominalRead383 (ForgetExactRule384 source) direct tagged s row) ∧
    Nonempty (ExactSelected384 source ordinary tagged s q d) ∧
    LogicalTaggedUnaryOutput383 tagged s q d ordinal row ∧
    ∀ m, Fits s m → Seen m.assignment m.authoredValues row := by
  obtain ⟨⟨proof⟩,linked,live⟩ :=
    tagged_exact_support_details384 (exact_support_at384 support pos atIndex)
  let read : TaggedNominalRead383 (ForgetExactRule384 source) direct tagged s row :=
    .output q d ordinal (erase_exact_selected384 proof) linked live
  exact ⟨⟨read⟩,⟨proof⟩,linked,fun m fit => tagged_nominal_read_seen_in_same_model383 read m fit⟩

/-- Local inversion exposes the two ordered lists separately and
retains the exact successful dictionary at the current node. -/
theorem exact_selected_local_inversion384 {source ordinary tagged s q d}
    (selected : ExactSelected384 source ordinary tagged s q d) :
    ∃ needs key kids whereDicts,
      d = .node key whereDicts ∧ source s q needs key kids ∧
      Nonempty (ExactSupportForest384 source ordinary tagged s needs) ∧
      Nonempty (ExactWhereForest384 source ordinary tagged s kids whereDicts) := by
  cases selected with
  | selected localRule reads whereProofs =>
    exact ⟨_,_,_,_,rfl,localRule,⟨reads⟩,⟨whereProofs⟩⟩

end Yulang.GeneralDeclarativeI65
