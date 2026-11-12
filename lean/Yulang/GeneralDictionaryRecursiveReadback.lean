import Yulang.GeneralNominalRecursiveCandidates
import Yulang.GeneralDictionaryNominalCandidateReadback
import Yulang.GeneralDictionaryPayloadReconstruction

/-!
# Exact source readback for recursive nominal candidates

Frames are computed from recursive inspection, retaining repeated capture merges,
compound observation paths, deterministic child identities and all child copies.
These theorems consume candidate derivations; they do not construct such a forest
or turn existential branch consistency into validity in every original model.
-/
namespace Yulang.GeneralDictionaryRecursiveReadback
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralNominalRecursiveCandidates (Context Survivor)
open GeneralDictionaryEmissionPlans (Frame Plan)
open GeneralDictionaryTransactions (Frames)

abbrev declaration := GeneralDictionaryNominalCandidateReadback.declaration
abbrev declaration_found := GeneralDictionaryNominalCandidateReadback.declaration_found

/-- Empty bindings make the frame total; survivor proofs rule out both failures. -/
def bindings (registry : Registry) (context : Context) (root : Occurrence registry.roles) (key : Nat) :
    GeneralNominalAllocation.Bindings :=
  match declaration registry root key, GeneralNominalRecursiveCandidates.arguments context root with
  | some selected, some bounds =>
      GeneralNominalRecursiveInspection.bindings context.state (GeneralNominalRecursiveCandidates.report context selected bounds)
  | _, _ => []

def frame (registry : Registry) (context : Context) (root : Occurrence registry.roles) : Frame registry.roles :=
  { GeneralNominalAllocation.frame context.state registry root.identity [] with
    capture := fun key => GeneralNominalAllocation.capture context.state registry root.identity key
      (bindings registry context root key) }

def frames (registry : Registry) (context : Context) : Frames registry.roles := frame registry context

theorem bindings_found (registry : Registry) (checked : Checked registry) (context : Context)
    (root : Occurrence registry.roles) (key : Nat) (selected : Declaration)
    (visible : selected ∈ registry.declarations) (identity : selected.id = key)
    (role : selected.role = root.demand.role)
    (bounds : List (GeneralNominalInspection.Bounds context.state))
    (located : GeneralNominalRecursiveCandidates.arguments context root = some bounds) :
    bindings registry context root key =
      GeneralNominalRecursiveInspection.bindings context.state (GeneralNominalRecursiveCandidates.report context selected bounds) := by
  rw [bindings, declaration, declaration_found registry checked root key selected visible identity role, located]

/-- Actual candidate emissions equal the complete plan under the computed frame. -/
theorem survivor_plan (registry : Registry) (checked : Checked registry) (context : Context)
    (root : Occurrence registry.roles) (key : Nat) (children : List (Occurrence registry.roles))
    (survivor : Survivor registry context root key children) :
    Plan registry checked (frames registry context root) root key children := by
  obtain ⟨_, selected, visible, selectedChecked, identity, role, bounds, located, _, emitted⟩ := survivor
  refine ⟨selected, visible, identity, role, ?_⟩
  rw [emitted]
  have found := bindings_found registry checked context root selected.id selected visible rfl role bounds located
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
  simp only [frames, frame, GeneralNominalAllocation.frame]
  rw [found]
  rfl

/-- Every independently justified candidate node retains the same indexed tree. -/
theorem evidence_plan (registry : Registry) (checked : Checked registry) (context : Context)
    (tree : Dictionary registry.roles) (evidence : Evidence (Survivor registry context) tree) :
    Evidence (GeneralDictionaryPayloadReconstruction.Rule registry checked (frames registry context)) tree :=
  evidence_mono _ _ (survivor_plan registry checked context) evidence

/-- No descendant occurrences or resolved Frames are supplied to this executor. -/
def reconstruct (registry : Registry) (checked : Checked registry) (context : Context)
    (payload : Payload) (root : Occurrence registry.roles) : Option (Dictionary registry.roles) :=
  GeneralDictionaryPayloadReconstruction.reconstruct registry checked (frames registry context) payload root

theorem reconstruct_candidate (registry : Registry) (checked : Checked registry) (context : Context)
    (tree : Dictionary registry.roles) (evidence : Evidence (Survivor registry context) tree) :
    reconstruct registry checked context (erase tree) tree.root = some tree :=
  GeneralDictionaryPayloadReconstruction.reconstruct_complete registry checked (frames registry context) tree
    (evidence_plan registry checked context tree evidence)

/-- Given candidate evidence at every node, reconstruction recovers that evidence
with exact source identity and raw payload. Existence of the derivation is a premise. -/
theorem payload_candidate_readback (registry : Registry) (checked : Checked registry) (context : Context)
    (root : Occurrence registry.roles) (payload : Payload)
    (evidence : PayloadEvidence (Survivor registry context) root payload) :
    ∃ tree, reconstruct registry checked context payload root = some tree ∧
      Readback root payload tree ∧ Evidence (Survivor registry context) tree := by
  obtain ⟨tree, readback, indexed⟩ := payload_to_indexed (Survivor registry context) payload root evidence
  refine ⟨tree, ?_, readback, indexed⟩
  rw [← readback.1, ← readback.2]
  exact reconstruct_candidate registry checked context tree indexed

/-- All valid candidate witnesses at this root/raw payload coincide. -/
theorem payload_candidate_unique (registry : Registry) (checked : Checked registry) (context : Context)
    (root : Occurrence registry.roles) (payload : Payload)
    (evidence : PayloadEvidence (Survivor registry context) root payload) :
    ∃ tree, reconstruct registry checked context payload root = some tree ∧
      Readback root payload tree ∧ Evidence (Survivor registry context) tree ∧
      ∀ other, Readback root payload other → Evidence (Survivor registry context) other → other = tree := by
  obtain ⟨tree, reconstructed, readback, indexed⟩ := payload_candidate_readback registry checked context root payload evidence
  refine ⟨tree, reconstructed, readback, indexed, ?_⟩
  intro other otherReadback otherEvidence
  exact indexed_unique (Survivor registry context)
    (GeneralNominalRecursiveCandidates.survivor_children_functional registry checked context)
    other tree (otherReadback.1.trans readback.1.symm) (otherReadback.2.trans readback.2.symm) otherEvidence indexed

end Yulang.GeneralDictionaryRecursiveReadback
