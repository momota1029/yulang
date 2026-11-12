import Yulang.GeneralDictionaryPayloadPreparation

/-!
# Fixed-input order invariance of raw-payload reconstruction and preparation

Allowed visible-declaration and where-clause reordering preserves the entire
optional result, including failures. The source root, raw selected-key payload,
frames and shared state are fixed. No candidate search or driver independence
is asserted, and arbitrary payload-child permutation is not authorized here.
-/
namespace Yulang.GeneralDictionaryPayloadReconstructionOrder
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralDictionaryTransactions (Frames)
open GeneralDictionaryPayloadReconstruction

/-- Actual Plan evidence moves in both directions under the supported registry
reordering, at every source occurrence's own frame. -/
theorem evidence_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (tree : Dictionary roles) :
    Evidence (Rule ⟨constructors, roles, first⟩ one frames) tree ↔
      Evidence (Rule ⟨constructors, roles, last⟩ two frames) tree := by
  constructor
  · exact evidence_mono _ _ (fun root key children =>
      (GeneralDictionaryEmissionPlans.plan_reorders_iff constructors roles first last one two order
        (frames root) root key children).mp)
  · exact evidence_mono _ _ (fun root key children =>
      (GeneralDictionaryEmissionPlans.plan_reorders_iff constructors roles first last one two order
        (frames root) root key children).mpr)

/-- Registry order cannot change reconstructed source identities or silently
change a structural failure into success for the fixed raw dictionary. -/
theorem reconstruct_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (frames : Frames roles) (payload : Payload) (root : Occurrence roles) :
    reconstruct ⟨constructors, roles, first⟩ one frames payload root =
      reconstruct ⟨constructors, roles, last⟩ two frames payload root := by
  cases found : reconstruct ⟨constructors, roles, first⟩ one frames payload root with
  | none =>
    cases other : reconstruct ⟨constructors, roles, last⟩ two frames payload root with
    | none => rfl
    | some tree =>
      obtain ⟨readback, evidence⟩ := (reconstruct_exact _ _ _ _ _ _).mp other
      have back := (reconstruct_exact _ one frames payload root tree).mpr
        ⟨readback, (evidence_reorders constructors roles first last one two order frames tree).mpr evidence⟩
      rw [found] at back
      cases back
  | some tree =>
    obtain ⟨readback, evidence⟩ := (reconstruct_exact _ _ _ _ _ _).mp found
    exact ((reconstruct_exact _ two frames payload root tree).mpr
      ⟨readback, (evidence_reorders constructors roles first last one two order frames tree).mp evidence⟩).symm

/-- The complete computed preparation package is fixed, hence so are its
source dictionary, emitted equation batch and recorded shared state. -/
theorem prepare_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (state : GeneralSourceState.State) (frames : Frames roles) (payload : Payload) (root : Occurrence roles) :
    GeneralDictionaryPayloadPreparation.prepare ⟨constructors, roles, first⟩ one state frames payload root =
      GeneralDictionaryPayloadPreparation.prepare ⟨constructors, roles, last⟩ two state frames payload root := by
  unfold GeneralDictionaryPayloadPreparation.prepare
  rw [reconstruct_reorders constructors roles first last one two order frames payload root]
  cases found : reconstruct ⟨constructors, roles, last⟩ two frames payload root with
  | none => rfl
  | some tree =>
    exact GeneralDictionarySourceRecipe.prepare_reorders constructors roles first last one two order state frames
      (GeneralDictionaryRecipeFidelity.recipe tree)

end Yulang.GeneralDictionaryPayloadReconstructionOrder
