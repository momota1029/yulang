import Yulang.GeneralDictionaryPlanLookup
import Yulang.GeneralDictionaryModelEvidence
import Yulang.GeneralDictionarySemanticOrder

/-!
# Actual declaration plans coupled to stored all-model dictionary equations

Children now come from the real checked registry and canonical emitter, not an
arbitrary local relation. The remaining explicit relation connects declarations
to Located head/output terms. It must still be implemented by actual source
instantiation. No head matcher, feasibility decision, frame or allocator is
invented, and this does not claim full general role Evidence.
-/
namespace Yulang.GeneralDictionaryPlannedEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralDictionaryEmissionPlans GeneralDictionaryPlanLookup GeneralDictionaryModelEvidence
open GeneralDictionaryStateEquations GeneralDictionarySemanticOrder
open GeneralSourceState (State Assignment Models)
open CommonRoleOutermostResolver (All₂)

/-- The still-missing actual declaration/capture-to-ordinary-term interpretation.
It cannot choose, discard, or reorder child source obligations. -/
abbrev TermInstances (roles : Roles.RoleDecls) (state : State) :=
  (occurrence : Occurrence roles) → Nat → Located state occurrence.demand → Prop

def Planned (registry : Registry) (checked : Checked registry) (frame : Frame registry.roles)
    (terms : TermInstances registry.roles state) : Packages registry.roles state :=
  fun root key children located => Plan registry checked frame root key children ∧ terms root key located

/-- Child determinism is now proved from actual checked declaration IDs and the
fixed resolved frame, independently of the unfinished term interpretation. -/
theorem planned_children_functional (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (terms : TermInstances registry.roles state) :
    ChildrenFunctional (StoredInstance (Planned registry checked frame terms)) := by
  intro root key first last one two
  obtain ⟨_, ⟨plan₁, _⟩, _⟩ := one
  obtain ⟨_, ⟨plan₂, _⟩, _⟩ := two
  exact plan_children_functional registry checked frame root key first last plan₁ plan₂

/-- Actual executable lookup + actual stored inequalities + all child evidence.
There is no caller-supplied abstract child-generation predicate. -/
theorem lookup_node_stored (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (terms : TermInstances registry.roles state)
    (root : Occurrence registry.roles) (key : Nat) (children : List (Occurrence registry.roles))
    (dictionaries : List Payload) (located : Located state root.demand)
    (found : lookup registry checked frame root key = some children)
    (interpreted : terms root key located) (recorded : Recorded located)
    (childrenStored : All₂ (PayloadEvidence (StoredInstance (Planned registry checked frame terms))) children dictionaries) :
    PayloadEvidence (StoredInstance (Planned registry checked frame terms)) root (.node key dictionaries) :=
  .node ⟨located, ⟨(lookup_exact registry checked frame root key children).mp found, interpreted⟩, recorded⟩ childrenStored

/-- One arbitrary actual shared-state model satisfies all generated node equations. -/
theorem lookup_node_all_models (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (terms : TermInstances registry.roles state)
    (root : Occurrence registry.roles) (key : Nat) (children : List (Occurrence registry.roles))
    (dictionaries : List Payload) (located : Located state root.demand)
    (found : lookup registry checked frame root key = some children)
    (interpreted : terms root key located) (recorded : Recorded located)
    (childrenStored : All₂ (PayloadEvidence (StoredInstance (Planned registry checked frame terms))) children dictionaries)
    (assignment : Assignment) (model : Models state assignment) :
    PayloadEvidence (ModelInstance (Planned registry checked frame terms) assignment) root (.node key dictionaries) :=
  payload_all_models _ root _
    (lookup_node_stored registry checked frame terms root key children dictionaries located found interpreted recorded childrenStored)
    assignment model

/-- Fixed-root key payloads reconstruct a unique full source witness because the
real declaration plan, rather than an assumed arbitrary local rule, fixes children. -/
theorem planned_unique_readback (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (terms : TermInstances registry.roles state)
    (root : Occurrence registry.roles) (payload : Payload)
    (stored : PayloadEvidence (StoredInstance (Planned registry checked frame terms)) root payload) :
    ∃ tree, (Readback root payload tree ∧ Evidence (StoredInstance (Planned registry checked frame terms)) tree) ∧
      ∀ other, Readback root payload other → Evidence (StoredInstance (Planned registry checked frame terms)) other → other = tree :=
  payload_unique_readback _ (planned_children_functional registry checked frame terms) root payload stored

/-- The same concrete source witness works in all final models, even after a
source-preserving sibling permutation of the key payload. -/
theorem planned_reordered_uniform (registry : Registry) (checked : Checked registry)
    (frame : Frame registry.roles) (terms : TermInstances registry.roles state)
    (root : Occurrence registry.roles) (before after : Payload)
    (same : GeneralDictionaryPayloadOrder.Equivalent before after)
    (stored : PayloadEvidence (StoredInstance (Planned registry checked frame terms)) root before) :
    ∃ tree, Readback root after tree ∧
      ∀ assignment, Models state assignment →
        Evidence (ModelInstance (Unordered (Planned registry checked frame terms)) assignment) tree :=
  equivalent_uniform_witness _ root before after same stored

end Yulang.GeneralDictionaryPlannedEvidence
