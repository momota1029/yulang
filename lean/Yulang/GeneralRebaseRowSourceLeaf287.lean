import Yulang.GeneralRebaseRowEvidenceAt287
import Yulang.GeneralRebaseRowMinimal287

/-! Regression for a possible precise settlement extension. The positive
leaf's certificate is independent of the full parent output; testing that
using a raw source assignment avoids circular trust through full Models.
This file does not modify any operational rule. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 15000000
namespace Yulang.GeneralRebaseRowSourceLeaf287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowChildRaw287 (SourceCheck before_exact)
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowGeneratedChild287 (current not_prepared)
open GeneralRebaseRowWholeChild287
open GeneralRebaseRowTrustedBoundary287 (raw_after)
open GeneralRebaseRowLocal287 (child_at_role)
open GeneralNominalVersionedPlans231 (Holds Outputs emittedSchema)
open GeneralNominalVersionedEvidence231 (Evidence Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalRecursiveInspection (ProjectionModels)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open CommonNominalFullCarrier

theorem holds_from_raw (m : Assignment) (valid : GeneralNominalState.Models (current true).state m) : Holds plan m := by
  refine ⟨valid,⟨ordinary m,?_,?_,?_,?_,?_,?_⟩,?_⟩
  · rw [report_exact]
    simp [ProjectionModels]
  · intro i
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro name used
    have eq : name = 0 := by
      rcases used with inHead|⟨_,member,_⟩
      · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
          GeneralDeclarationPatterns.Pattern.variables] using inHead
      · cases member
    subst name
    change GeneralNominalCaptureMerges.Fits m ((GeneralNominalVersionedFrame231.capture packet).inputs 0)
      (m (GeneralNominalVersionedFrame231.binder plan 0)).1
    rw [binder,capture]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    refine ⟨(by intro _ impossible; cases impossible),?_⟩
    intro entry member
    cases List.mem_singleton.mp member
    simp only [ite_true,binder]
    exact GeneralNominalOriginTerms.source_self m 0
  · rw [emitted_empty]
    intro _ h; cases h
  · intro _ h; cases h
  · unfold Outputs
    rw [emitted_empty]
    intro _ h; cases h

def SourceVerifiedLeaf (choice : Bool) : Prop :=
  ∃ p : Plan roles, Frame (registry choice) (after choice).core (child choice) 1 p ∧
    GeneralNominalVersionedFrame231.children p.packet = [] ∧
    GeneralNominalCenteredHeadMatEffects.Ready (after choice).core (child choice) p ∧
    ∀ m, SourceCheck m → Holds p m ∧
      GeneralNominalVersionedEffects231.ClassEffects (after choice).core (child choice) p m

theorem source_verified : SourceVerifiedLeaf true :=
  ⟨plan,child_frame,no_children,ready,fun m source =>
    ⟨holds_from_raw m ((raw_after true m).mpr source),class_effects m⟩⟩

theorem excluded : ¬ SourceVerifiedLeaf false := by
  rintro ⟨p,f,_,_,_⟩
  have ready := f.prepared
  rw [child_at_role false _ f.visible f.role_eq] at ready
  exact not_prepared ready

theorem output_independent_leaf :
    ∃ m, Models before m ∧ ¬ Models (after true) m ∧
      Evidence (registry true) (after true).core m (child true) (.node 1 []) := by
  let m := GeneralRebaseRowMinimal287.changeType (model Common.rowEmpty) 2
  have source : SourceCheck m :=
    (before_exact (model Common.rowEmpty)).mp (before_model Common.rowEmpty)
  refine ⟨m,(before_exact m).mpr source,GeneralRebaseRowMinimal287.after_loss true 2 (by decide),?_⟩
  exact GeneralNominalVersionedEvidence231.evidence_leaf
    ⟨plan,GeneralNominalVersionedEvidence231.certificate_of_semantics child_frame no_children.symm
      (holds_from_raw m ((raw_after true m).mpr source)) ready (class_effects m)⟩

end Yulang.GeneralRebaseRowSourceLeaf287
