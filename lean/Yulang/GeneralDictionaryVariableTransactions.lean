import Yulang.GeneralDictionaryVariablePlans

/-!
# Whole source dictionary transactions with computed output interpretation

At every node the complete child plan and output terms are computed together
from the same visible checked declaration. Only head interpretation and resolved
source frames remain abstract. A single recorded transaction constructs all
storage evidence and one fixed source witness before quantifying over models.
Exact-input aliases can terminate output-bearing trees without choosing a midpoint.
This is not a candidate solver or a general-source B4 instance.
-/
namespace Yulang.GeneralDictionaryVariableTransactions
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralDictionaryEmissionPlans GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs)
open GeneralDictionaryVariablePlans
open GeneralDictionaryTransactions (Frames Prepared Valid PlannedAt LiftedTerms)
open GeneralDictionaryModelEvidence (StoredInstance ModelInstance)
open GeneralDictionaryBatchRecording (record)
open GeneralSourceState (State Assignment Models)

variable {state : State}

/-- A source tree whose output side is built, not provided as an interpretation
certificate. Complete child roots must equal the actual canonical emission. -/
inductive Built (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state) :
    Prepared registry.roles state → Prop where
  | node {root : Occurrence registry.roles} {key : Nat}
      (inputs : Inputs state root.demand) (result : Result state root)
      (children : List (Prepared registry.roles state))
      (found : lookup registry checked (frames root) root key inputs = some result)
      (head : ∀ declaration ∈ registry.declarations,
        declaration.id = key → declaration.role = root.demand.role →
          heads root declaration ((frames root).capture declaration.id) inputs.head)
      (complete : children.map Prepared.root = result.children)
      (childrenBuilt : ∀ child ∈ children, Built registry checked frames heads child) :
      Built registry checked frames heads (.node root key result.located children)

/-- No arbitrary output-side TermInstances premise is left in the tree. -/
theorem built_valid (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (tree : Prepared registry.roles state) (built : Built registry checked frames heads tree) :
    Valid registry checked frames (Terms registry frames heads) tree := by
  induction built with
  | @node root key inputs result children found head complete childrenBuilt ih =>
      apply Valid.node
      · rw [complete]
        exact lookup_plan registry checked (frames root) root key inputs result found
      · exact lookup_terms registry checked frames heads root key inputs result found head
      · exact ih

theorem transaction_stored (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (tree : Prepared registry.roles state) (built : Built registry checked frames heads tree) :
    Evidence (StoredInstance (PlannedAt registry checked frames
      (LiftedTerms tree.items (Terms registry frames heads)))) tree.dictionary :=
  GeneralDictionaryTransactions.transaction_stored registry checked frames _ tree
    (built_valid registry checked frames heads tree built)

/-- Semantics in the original source coordinates, independent of where the
transaction stores its local copy of each Located package. -/
def SourceInstance (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (assignment : Assignment) : LocalInstance registry.roles :=
  fun root key children => ∃ located : Located state root.demand,
    Plan registry checked (frames root) root key children ∧
    Terms registry frames heads root key located ∧ located.equations.Holds assignment

/-- Relocation preserves the actual source equations; no term interpretation is
recomputed against a different state or a differently chosen declaration. -/
theorem lifted_source_instance (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (items : List (GeneralDictionaryBatchRecording.Item registry.roles state))
    (assignment : Assignment) (root : Occurrence registry.roles) (key : Nat)
    (children : List (Occurrence registry.roles))
    (instanceRule : ModelInstance (PlannedAt registry checked frames
      (LiftedTerms items (Terms registry frames heads))) assignment root key children) :
    SourceInstance registry checked frames heads assignment root key children := by
  obtain ⟨located, ⟨plan, original, terms, same⟩, holds⟩ := instanceRule
  subst located
  exact ⟨original, plan, terms, holds⟩

/-- One source witness, uniform in every joint model of the complete batch.
All output meaning is actual declaration provenance; heads remain explicit. -/
theorem transaction_uniform (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (tree : Prepared registry.roles state) (built : Built registry checked frames heads tree) :
    ∃ witness, Readback tree.root (erase tree.dictionary) witness ∧
      ∀ assignment, Models (record tree.items) assignment →
        Evidence (SourceInstance registry checked frames heads assignment) witness := by
  refine ⟨tree.dictionary, ⟨GeneralDictionaryTransactions.dictionary_root tree, rfl⟩, ?_⟩
  intro assignment model
  have allModels := GeneralDictionaryModelEvidence.indexed_all_models _ tree.dictionary
    (transaction_stored registry checked frames heads tree built) assignment model
  exact evidence_mono _ _ (lifted_source_instance registry checked frames heads tree.items assignment) allModels

/-- The declaration supplying output denotation is exactly the one supplying
the complete canonical child list. The equality follows from checked visible IDs. -/
theorem source_instance_declaration (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (assignment : Assignment) (root : Occurrence registry.roles) (key : Nat)
    (children : List (Occurrence registry.roles))
    (instanceRule : SourceInstance registry checked frames heads assignment root key children) :
    ∃ declaration, ∃ present : declaration ∈ registry.declarations,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      children = GeneralDictionaryEmissionPlans.children (frames root) root declaration
        (checked.2 declaration present) ∧
      ∃ located : Located state root.demand,
        heads root declaration ((frames root).capture declaration.id) located.head ∧
        GeneralDictionaryVariableTerms.Interpreted declaration
          ((frames root).capture declaration.id) located ∧ located.equations.Holds assignment := by
  obtain ⟨located, ⟨first, firstPresent, firstKey, _, generated⟩,
    ⟨declaration, present, identity, role, head, output⟩, holds⟩ := instanceRule
  have equal := declaration_key_unique registry checked first declaration firstPresent present
    (firstKey.trans identity.symm)
  subst first
  exact ⟨declaration, present, identity, role, generated, located, head, output, holds⟩

/-- An actual explicit RHS of the same checked visible declaration explains
each root output in every model, with all source occurrences retained. -/
theorem source_output_denotes (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (heads : HeadInstances registry.roles state)
    (assignment : Assignment) (root : Occurrence registry.roles) (key : Nat)
    (children : List (Occurrence registry.roles))
    (instanceRule : SourceInstance registry checked frames heads assignment root key children)
    (index : Fin root.demand.outputs.length) :
    ∃ declaration, ∃ present : declaration ∈ registry.declarations,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      children = GeneralDictionaryEmissionPlans.children (frames root) root declaration
        (checked.2 declaration present) ∧
      ∃ term, GeneralDictionaryVariableTerms.Denotes registry.roles declaration
        ((frames root).capture declaration.id) (root.demand.outputs[index]).name term ∧
        Common.Equivalent (assignment (root.demand.outputs[index]).target).1
          (term.eval Common.model assignment) := by
  obtain ⟨declaration, present, identity, role, generated, located, _, outputs, holds⟩ :=
    source_instance_declaration registry checked frames heads assignment root key children instanceRule
  refine ⟨declaration, present, identity, role, generated, located.equations.output index, ?_, holds.2 index⟩
  exact (GeneralDictionaryVariableTerms.lookup_exact registry.roles declaration _
    (checked.2 declaration present).identified.2.2.1 _ _).mp (outputs index)

end Yulang.GeneralDictionaryVariableTransactions
