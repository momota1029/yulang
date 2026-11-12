import Yulang.GeneralDictionaryNominalCandidateEvidence
import Yulang.GeneralDictionaryPayloadReconstructionOrder

/-!
# Computed nominal frames under checked registry reordering

At one fixed candidate context, visible and where-clause reordering preserves
computed bindings and frames. Consequently the no-caller-Frames reconstruction
and partial preparation wrappers return exactly the same optional result.
This does not equate propagated states, successor contexts, candidate forests,
or arbitrary raw-payload child permutations, and is not general B4.
-/
namespace Yulang.GeneralDictionaryNominalCandidateOrder
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralNominalCandidates (Context)
open GeneralDictionaryNominalCandidateReadback

/-- Inspection depends on the unchanged head, not the where enumeration. -/
theorem report_reorders (context : Context) (first last : Declaration)
    (order : GeneralRegistryReordering.DeclarationReorders first last)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    GeneralNominalCandidates.report context first bounds =
      GeneralNominalCandidates.report context last bounds := by
  simp only [GeneralNominalCandidates.report, GeneralNominalInspection.queries,
    Declaration.normalHead, order.head]

/-- Successful lookup moves to the corresponding full declaration; the full
selected declarations need not be equal because their where lists can differ. -/
theorem declaration_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (two : Checked ⟨constructors, roles, last⟩)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (root : Occurrence roles) (key : Nat) (selected : Declaration)
    (found : declaration ⟨constructors, roles, first⟩ root key = some selected) :
    ∃ other, declaration ⟨constructors, roles, last⟩ root key = some other ∧
      GeneralRegistryReordering.DeclarationReorders selected other := by
  have present := List.mem_of_find?_eq_some found
  have properties : selected.id = key ∧ selected.role = root.demand.role := by
    simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some found
  obtain ⟨other, visible, pair⟩ := GeneralRegistryReordering.reorders_visible order selected present
  exact ⟨other, declaration_found _ two root key other visible
    (pair.id.symm.trans properties.1) (pair.role.symm.trans properties.2), pair⟩

/-- Failed key/role lookup remains failed, including absent declarations. -/
theorem declaration_none_reorders (constructors : GeneralDeclarationPatterns.Constructors)
    (roles : Roles.RoleDecls) (first last : List Declaration)
    (order : GeneralRegistryReordering.Reorders ⟨constructors, roles, first⟩ ⟨constructors, roles, last⟩)
    (root : Occurrence roles) (key : Nat)
    (absent : declaration ⟨constructors, roles, first⟩ root key = none) :
    declaration ⟨constructors, roles, last⟩ root key = none := by
  cases found : declaration ⟨constructors, roles, last⟩ root key with
  | none => rfl
  | some selected =>
    have present := List.mem_of_find?_eq_some found
    have properties : selected.id = key ∧ selected.role = root.demand.role := by
      simpa only [Bool.and_eq_true, beq_iff_eq] using List.find?_some found
    obtain ⟨other, visible, pair⟩ := GeneralRegistryReordering.reorders_visible_back order selected present
    have impossible := List.find?_eq_none.mp absent other visible
    simp only [pair.id, pair.role, properties.1, properties.2, beq_self_eq_true,
      Bool.and_self, not_true_eq_false] at impossible

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
    simp only [bindings, found, other]
  | some selected =>
    obtain ⟨other, located, pair⟩ := declaration_reorders constructors roles first last two order root key selected found
    cases arguments : GeneralNominalCandidates.arguments context root with
    | none => simp only [bindings, found, located, arguments]
    | some bounds =>
      simp only [bindings, found, located, arguments, report_reorders context selected other pair bounds]

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
    GeneralDictionaryNominalCandidateEvidence.prepare ⟨constructors, roles, first⟩ one context payload root =
      GeneralDictionaryNominalCandidateEvidence.prepare ⟨constructors, roles, last⟩ two context payload root := by
  unfold GeneralDictionaryNominalCandidateEvidence.prepare
  rw [frames_reorders constructors roles first last two order context]
  exact GeneralDictionaryPayloadReconstructionOrder.prepare_reorders
    constructors roles first last one two order context.state.base _ payload root

end Yulang.GeneralDictionaryNominalCandidateOrder
