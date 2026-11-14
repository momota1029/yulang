import Yulang.GeneralNominalTwoHeadNonvacuity190
import Yulang.GeneralNominalInstallationSound190

/-! The operational residual used by the recursive soundness bridge is inhabited
on the actual two-head named-output source, although not valid on every source.
The final evidence below goes through the recursive V6 theorem. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalAvailableNonvacuity190
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalTwoHeadFixture190 GeneralNominalTwoHeadNonvacuity190
open GeneralNominalInstallationSound190
open GeneralNominalCenteredHeadWFBoundary (boundary)

theorem available : Available registry start root := by
  intro focus generated key kids chosen
  have same : focus = root := by
    induction generated with
    | root => rfl
    | child _ member _ => cases member
    | alias _ _ member _ _ =>
      exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp member)
  subst focus
  apply GeneralNominalSourceLinearEvidence190.selected_source_candidate checked initial_source chosen
  intro d member _
  cases List.mem_singleton.mp member
  refine ⟨⟨[0,1],by decide +kernel,rfl⟩,rfl,?_,?_⟩
  · intro output member
    cases List.mem_singleton.mp member
    exact ⟨⟨0,0,.var 0⟩,List.mem_singleton_self _,rfl⟩
  · intro equation member
    cases List.mem_singleton.mp member
    simp [GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralNominalHeadMatchMass.Complete]

theorem classified : B4TargetV6.Classify (boundary roles) registry start root (.selected (.node 3 [])) := by
  apply B4TargetV6.Classify.selected safe
    (show B4TargetV6.Unique (boundary roles) registry start root 3 [] from by
      change GeneralNominalCenteredHeadCandidates.Unique registry context root 3 []
      simpa only [GeneralNominalHeadLeafPlan189.children_empty plan rfl] using unique)
    no_output_conflict
  exact .nil

theorem recursive_evidence : (boundary roles).Evidence registry start model root (.node 3 []) :=
  dictionary_evidence root stable available model inhabited (.node 3 []) root .root classified

end Yulang.GeneralNominalAvailableNonvacuity190
