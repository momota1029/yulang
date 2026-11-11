import Yulang.GeneralDictionaryReadback
import Yulang.GeneralDictionaryStateEquations

/-!
# Whole-dictionary equation evidence from actual shared-state storage

Packages retain their source occurrence, implementation key, exact children and
located head/output terms. Storage is checked in the actual State. Every model
of that State satisfies all equations at every node of the indexed or erased
finite dictionary. The package relation still has to be derived from actual
declaration instances: this is equation evidence, not completed role semantics.
-/
namespace Yulang.GeneralDictionaryModelEvidence
open GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralDictionaryStateEquations
open GeneralSourceState (State Assignment Models)

/-- The relation must eventually connect terms to real declarations/captures.
Located source IDs and actual storage cannot substitute for that missing bridge. -/
abbrev Packages (roles : Roles.RoleDecls) (state : State) :=
  (occurrence : Occurrence roles) → Nat → List (Occurrence roles) →
    Located state occurrence.demand → Prop

def StoredInstance (packages : Packages roles state) : LocalInstance roles :=
  fun occurrence key children =>
    ∃ located, packages occurrence key children located ∧ Recorded located

def ModelInstance (packages : Packages roles state) (assignment : Assignment) : LocalInstance roles :=
  fun occurrence key children =>
    ∃ located, packages occurrence key children located ∧ located.equations.Holds assignment

/-- No semantic all-model premise is assumed: Recorded is membership of the four
families of generated inequalities in the concrete shared ordinary state. -/
theorem stored_instance_models (packages : Packages roles state)
    (assignment : Assignment) (model : Models state assignment)
    (occurrence : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (stored : StoredInstance packages occurrence key children) :
    ModelInstance packages assignment occurrence key children := by
  obtain ⟨located, instanceRule, recorded⟩ := stored
  exact ⟨located, instanceRule, recorded_holds located recorded assignment model⟩

/-- One shared arbitrary model satisfies all nodes simultaneously, including
repeated named outputs. It is not a separate witness model for each child. -/
theorem indexed_all_models (packages : Packages roles state) (tree : Dictionary roles)
    (stored : Evidence (StoredInstance packages) tree) (assignment : Assignment)
    (model : Models state assignment) : Evidence (ModelInstance packages assignment) tree :=
  evidence_mono _ _ (stored_instance_models packages assignment model) stored

/-- The same exact source-indexed witness works for every model of the shared
state. The existential is outside the universal model quantifier. -/
theorem erased_uniform_witness (packages : Packages roles state) (occurrence : Occurrence roles)
    (payload : Payload) (stored : ErasedEvidence (StoredInstance packages) occurrence payload) :
    ∃ tree, Readback occurrence payload tree ∧
      ∀ assignment, Models state assignment → Evidence (ModelInstance packages assignment) tree := by
  obtain ⟨tree, readback, evidence⟩ := stored
  exact ⟨tree, readback, indexed_all_models packages tree evidence⟩

/-- Source identities are not dropped from the independent semantic judgment,
even though the execution payload itself contains only keys and child payloads. -/
theorem payload_all_models (packages : Packages roles state) (occurrence : Occurrence roles)
    (payload : Payload) (stored : PayloadEvidence (StoredInstance packages) occurrence payload)
    (assignment : Assignment) (model : Models state assignment) :
    PayloadEvidence (ModelInstance packages assignment) occurrence payload := by
  obtain ⟨tree, ⟨root, erased⟩, evidence⟩ := payload_to_indexed _ _ _ stored
  have sound := indexed_all_models packages tree evidence assignment model
  simpa only [root, erased] using indexed_to_payload _ tree sound

/-- Concrete declaration packages can discharge deterministic-child readback
without pretending that arbitrary SourceBoundary predicates have this property. -/
theorem stored_children_functional (packages : Packages roles state)
    (deterministic : ∀ occurrence key first last located₁ located₂,
      packages occurrence key first located₁ → packages occurrence key last located₂ → first = last) :
    ChildrenFunctional (StoredInstance packages) := by
  intro occurrence key first last h₁ h₂
  obtain ⟨located₁, instance₁, _⟩ := h₁
  obtain ⟨located₂, instance₂, _⟩ := h₂
  exact deterministic occurrence key first last located₁ located₂ instance₁ instance₂

/-- A key-only dictionary with stored equation evidence has exactly one valid
source witness when the actual local package determines its ordered children. -/
theorem stored_unique_readback (packages : Packages roles state)
    (deterministic : ∀ occurrence key first last located₁ located₂,
      packages occurrence key first located₁ → packages occurrence key last located₂ → first = last)
    (occurrence : Occurrence roles) (payload : Payload)
    (stored : PayloadEvidence (StoredInstance packages) occurrence payload) :
    ∃ tree, (Readback occurrence payload tree ∧ Evidence (StoredInstance packages) tree) ∧
      ∀ other, Readback occurrence payload other → Evidence (StoredInstance packages) other → other = tree :=
  payload_unique_readback _ (stored_children_functional packages deterministic) occurrence payload stored

end Yulang.GeneralDictionaryModelEvidence
