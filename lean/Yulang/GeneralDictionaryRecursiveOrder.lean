import Yulang.GeneralDictionaryRecursivePreparation
import Yulang.GeneralDictionaryNominalCandidateOrder
import Yulang.GeneralDictionaryPayloadReconstructionOrder

/-!
# Computed recursive nominal frames under checked registry reordering

At one fixed candidate context, visible and where-clause reordering preserves
computed bindings and frames. Consequently the no-caller-Frames reconstruction
and partial preparation wrappers return exactly the same optional result.
This does not equate propagated states, successor contexts, candidate forests,
or arbitrary raw-payload child permutations, and is not general B4.
-/
namespace Yulang.GeneralDictionaryRecursiveOrder
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralNominalCandidates (Context)
open GeneralDictionaryRecursiveReadback

/-- Inspection depends on the unchanged head, not the where enumeration. -/
theorem report_reorders (context : Context) (first last : Declaration)
    (order : GeneralRegistryReordering.DeclarationReorders first last)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    GeneralNominalRecursiveCandidates.report context first bounds =
      GeneralNominalRecursiveCandidates.report context last bounds := by
  simp only [GeneralNominalRecursiveCandidates.report, GeneralNominalInspection.queries,
    Declaration.normalHead, order.head]

abbrev declaration_reorders := GeneralDictionaryNominalCandidateOrder.declaration_reorders
abbrev declaration_none_reorders := GeneralDictionaryNominalCandidateOrder.declaration_none_reorders

/-- All fallback branches are included; no survivor premise is required. -/
theorem bindings_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (context : Context) (root : Occurrence roles) (key : Nat) :
    bindings ⟨constructors, roles, first⟩ context root key =
      bindings ⟨constructors, roles, last⟩ context root key := by
  cases found : declaration ⟨constructors, roles, first⟩ root key with
  | none =>
    have other := declaration_none_reorders constructors roles first last order root key found
    simp only [bindings, declaration, found, other]
  | some selected =>
    obtain ⟨other, located, pair⟩ := declaration_reorders constructors roles first last two order root key selected found
    cases arguments : GeneralNominalRecursiveCandidates.arguments context root with
    | none => simp only [bindings, declaration, found, located, arguments]
    | some bounds =>
      simp only [bindings, declaration, found, located, arguments, report_reorders context selected other pair bounds]

/-- Allocation origins and seed are fixed; registry enumeration is not read by
source allocation. No equality of reserved or ownership lists is asserted. -/
theorem frame_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (context : Context) (root : Occurrence roles) :
    frame ⟨constructors, roles, first⟩ context root =
      frame ⟨constructors, roles, last⟩ context root := by
  have equal : bindings ⟨constructors, roles, first⟩ context root =
      bindings ⟨constructors, roles, last⟩ context root :=
    funext (bindings_reorders constructors roles first last two order context root)
  simp only [frame, GeneralNominalAllocation.frame, equal,
    GeneralNominalAllocation.capture, GeneralNominalAllocation.source]
  rfl

/-- Equality at every occurrence, not just the outer root. -/
theorem frames_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (context : Context) :
    frames ⟨constructors, roles, first⟩ context =
      frames ⟨constructors, roles, last⟩ context :=
  funext (frame_reorders constructors roles first last two order context)

/-- Exact optional-result invariance without caller-supplied frames. -/
theorem reconstruct_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (context : Context) (payload : Payload) (root : Occurrence roles) :
    reconstruct ⟨constructors, roles, first⟩ one context payload root =
      reconstruct ⟨constructors, roles, last⟩ two context payload root := by
  unfold reconstruct
  rw [frames_reorders constructors roles first last two order context]
  exact GeneralDictionaryPayloadReconstructionOrder.reconstruct_reorders
    constructors roles first last one two order _ payload root

/-- Partial variable materialization keeps both success and failure unchanged
at the fixed base snapshot. This does not prove materialization completeness. -/
theorem prepare_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (one : Checked ⟨constructors, roles, first⟩) (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (context : Context) (payload : Payload) (root : Occurrence roles) :
    GeneralDictionaryRecursivePreparation.prepare ⟨constructors, roles, first⟩ one context payload root =
      GeneralDictionaryRecursivePreparation.prepare ⟨constructors, roles, last⟩ two context payload root := by
  unfold GeneralDictionaryRecursivePreparation.prepare
  rw [frames_reorders constructors roles first last two order context]
  exact GeneralDictionaryPayloadReconstructionOrder.prepare_reorders
    constructors roles first last one two order context.state.base _ payload root

end Yulang.GeneralDictionaryRecursiveOrder
