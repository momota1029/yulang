import Yulang.GeneralDeclarativeI65ExactSupportReads384
import Yulang.GeneralDeclarativeI65SourceTree365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (Seen)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeHead320 (Equation)

/-- The still missing general local source adapter, isolated at the
*exact* pre-erasure rule. It receives the actual ordered output-read
premises with their producing proof trees, not completion guessed
from a dictionary or an unkeyed request list. It has no model premise. -/
def ProvidesExactSource384 (s : State) (source : ExactSelectedRule384)
    (ordinary : LogicalOutputEquation383) (tagged : ChosenTaggedBinding383) : Prop :=
  ∀ q needs key kids, source s q needs key kids →
    ExactSupportForest384 source ordinary tagged s needs →
    ∃ row : Declaration, row.id = key ∧ Nonempty (SourceNode s q row kids)

/-- On the existing C365 source-receipt carrier, lower an exact
finite proof without first erasing its local support. Only the where
forest contributes literal receipt rows; the provider may use exact
read provenance to construct the node. -/
theorem lower_exact_selected_to_source384
    {s source ordinary tagged q d}
    (provide : ProvidesExactSource384 s source ordinary tagged)
    (actual : ExactSelected384 source ordinary tagged s q d) :
    ∃ rows, SourceTree s q d rows := by
  exact ExactSelected384.rec
    (motive_1 := fun q d _ => ∃ rows, SourceTree s q d rows)
    (motive_2 := fun _ _ => True)
    (motive_3 := fun qs ds _ => ∃ rows, SourceForest s qs ds rows)
    (fun rule support _ _ whereIH => by
      obtain ⟨row,keyExact,⟨node⟩⟩ := provide _ _ _ _ rule support
      obtain ⟨later,lowered⟩ := whereIH
      subst_vars
      exact ⟨captureReceipt node :: later,.node node lowered⟩)
    True.intro
    (fun _ _ _ _ _ => True.intro)
    ⟨[],.nil⟩
    (fun _ _ first rest => by
      obtain ⟨now,left⟩ := first
      obtain ⟨later,right⟩ := rest
      exact ⟨now ++ later,.cons left right⟩)
    actual

/-- The fixed rows are the same witnesses for every fitting model,
not a newly produced packet per model. The local adapter and general
typed receipt carrier remain separate parts of Step 1. -/
theorem exact_lowering_remains_in_every_model384
    {s source ordinary tagged q d}
    (provide : ProvidesExactSource384 s source ordinary tagged)
    (actual : ExactSelected384 source ordinary tagged s q d) :
    ∃ rows, SourceTree s q d rows ∧
      ∀ m, Fits s m → TreeEvidence s m q d rows ∧
        ∀ receipt ∈ rows, ∀ eq ∈ receipt.rows, Holds m.assignment eq := by
  obtain ⟨rows,proof⟩ := lower_exact_selected_to_source384 provide actual
  exact ⟨rows,proof,fun m fit => by
    have evidence := source_tree_sound proof m fit
    exact ⟨evidence,every_fixed_row_comes_from_the_same_model evidence⟩⟩

/-- Semantic consequences of an exact supporting cell. Both
ordinary truth and tagged observed values are evaluated in the
same state/model; no conversion between the carriers is used. -/
def OutputNeed384.Meaning (m : Model) : OutputNeed384 → Prop
  | .ordinary _ _ _ row => Holds m.assignment row
  | .tagged _ _ _ row => Seen m.assignment m.authoredValues row

theorem exact_need_has_same_model_meaning384 {s source ordinary tagged needs}
    (forest : ExactSupportForest384 source ordinary tagged s needs)
    {need : OutputNeed384} (ordinal : Nat) (position : needs[ordinal]? = some need)
    (m : Model) (fit : Fits s m) : need.Meaning m := by
  have supported := exact_support_at384 forest ordinal position
  cases need with
  | ordinary q d i row =>
    have present := (ordinary_exact_support_details384 supported).2.2
    exact fit.1.1.2 row present
  | tagged q d i row =>
    have present := (tagged_exact_support_details384 supported).2.2
    exact fit.1.2 row present

end Yulang.GeneralDeclarativeI65
