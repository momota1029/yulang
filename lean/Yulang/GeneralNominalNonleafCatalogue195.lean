import Yulang.GeneralNominalSelectedCatalogue195
import Yulang.GeneralNominalNonleafFinal194

/-! The existing stable nonleaf example has a complete mixed catalogue with
one genuinely unrecorded reused child; original journal coverage is false. -/
namespace Yulang.GeneralNominalNonleafCatalogue195
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193
open GeneralNominalNonleafChild193
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralNominalReuseCatalogue195
open GeneralDictionaryJournalTree (Covered Reach)

noncomputable def plans : List (Plan roles) := [childPlan]

theorem reusable : ∀ p ∈ plans, Reusable registry finish p := by
  intro p member
  have same : p = childPlan := List.mem_singleton.mp member
  subst p
  refine ⟨frame,GeneralNominalSemanticNode194.request_ready frame GeneralNominalNonleafReuse193.ready ?_,
    GeneralNominalNonleafReuse193.committed⟩
  change (GeneralNominalPacketSupport.namedSchema childPlan.packet).unknown = false
  rw [GeneralNominalHeadLeafPlan189.named_schema_empty childPlan rfl rfl]

theorem packets_exact : (catalogue finish plans).packets = [packet,childPacket] := rfl

theorem child_empty : childPacket.children = [] :=
  GeneralNominalHeadLeafPlan189.children_empty childPlan rfl

theorem reached_cases {focus : Occurrence roles} (reached : Reach (catalogue finish plans) displayRoot focus) :
    focus = displayRoot ∨ focus = displayChild := by
  induction reached with
  | root => exact Or.inl rfl
  | @child parent focus prior edge ih =>
    obtain ⟨p,member,same,within⟩ := edge
    rw [packets_exact] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · change focus ∈ plan.packet.children at within
      rw [children_exact] at within
      exact Or.inr (List.mem_singleton.mp within)
    · rw [child_empty] at within
      cases within

theorem covered : Covered (catalogue finish plans) displayRoot := by
  intro focus reached
  rcases reached_cases reached with rfl | rfl
  · exact ⟨packet,by rw [packets_exact]; simp,rfl⟩
  · exact ⟨childPacket,by rw [packets_exact]; simp,rfl⟩

theorem ordinary_path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry displayRoot)
    start finish :=
  .tail .refl (GeneralNominalOrdinaryEvidence191.install_step enabled .root novel)

/-- Coverage of the actual journal fails, but the finite reuse catalogue is
complete and semantically valid without adding a new transition. -/
theorem genuine_reuse :
    ¬ Covered finish.core.erased.current displayRoot ∧
    Covered (catalogue finish plans) displayRoot ∧
    (∀ p ∈ plans, Reusable registry finish p) :=
  ⟨GeneralNominalRecordedNode194.not_covered,covered,reusable⟩

theorem uniform_dictionary :
    ∃ tree : Dictionary roles, tree.root = displayRoot ∧
      GeneralSourceDictionaries.Evidence (GeneralDictionaryJournalTree.Recorded (catalogue finish plans)) tree ∧
      ∀ model, Models finish model → (boundary roles).Evidence registry finish model displayRoot (erase tree) :=
  GeneralNominalReuseCatalogue195.uniform_dictionary ordinary_path reusable covered

/-- The particular selected payload is validated using the mixed catalogue,
not merely by choosing some other semantic dictionary. -/
theorem selected_sound : ∀ model, Models finish model →
    (boundary roles).Evidence registry finish model displayRoot (.node 1 [.node 3 []]) :=
  GeneralNominalSelectedCatalogue195.selected_sound ordinary_path reusable covered _
    GeneralNominalNonleafFinal194.parent_classify
end Yulang.GeneralNominalNonleafCatalogue195
