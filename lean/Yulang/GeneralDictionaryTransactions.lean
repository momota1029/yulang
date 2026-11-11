import Yulang.GeneralDictionaryBatchRecording
import Yulang.GeneralDictionaryPlannedEvidence

/-!
# Executable recording of a whole source dictionary

A finite annotated dictionary retains actual checked declaration plans and
Located equations at every node. Its transaction computes one batch for the
entire tree, records it, and constructs source evidence with no manual Recorded
premises. The declaration-term interpretation and resolved frame remain inputs.
This is not candidate selection, recursive search, or a general B4 instance.
-/
namespace Yulang.GeneralDictionaryTransactions
open GeneralSourceState (State Assignment Models)
open GeneralSourceDictionaries GeneralDictionaryReadback GeneralDictionaryModelEvidence
open GeneralDictionaryStateEquations GeneralDictionaryEmissionPlans GeneralDictionaryPlannedEvidence
open GeneralDeclarations
open GeneralDictionaryBatchRecording (Item record relocate)

/-- One resolved frame per actual source invocation. Reusing an implementation
key does not force different root occurrences to share captured endpoints. -/
abbrev Frames (roles : Roles.RoleDecls) := Occurrence roles → Frame roles

def PlannedAt (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (terms : TermInstances registry.roles state) :
    Packages registry.roles state :=
  fun root key children located =>
    Plan registry checked (frames root) root key children ∧ terms root key located

theorem plannedAt_children_functional (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (terms : TermInstances registry.roles state) :
    ChildrenFunctional (StoredInstance (PlannedAt registry checked frames terms)) := by
  intro root key first last one two
  obtain ⟨_, ⟨plan₁, _⟩, _⟩ := one
  obtain ⟨_, ⟨plan₂, _⟩, _⟩ := two
  exact plan_children_functional registry checked (frames root) root key first last plan₁ plan₂

inductive Prepared (roles : Roles.RoleDecls) (state : State) where
  | node (root : Occurrence roles) (key : Nat) (located : Located state root.demand)
      (children : List (Prepared roles state))

def Prepared.root : Prepared roles state → Occurrence roles
  | .node root _ _ _ => root

mutual
  def Prepared.dictionary : Prepared roles state → Dictionary roles
    | .node root key _ children => .node root key (dictionaries children)
  def dictionaries : List (Prepared roles state) → List (Dictionary roles)
    | [] => []
    | first :: rest => first.dictionary :: dictionaries rest
end

mutual
  def Prepared.items : Prepared roles state → List (Item roles state)
    | .node root _ located children => ⟨root.demand, located⟩ :: childItems children
  def childItems : List (Prepared roles state) → List (Item roles state)
    | [] => []
    | first :: rest => first.items ++ childItems rest
end

theorem dictionary_root (tree : Prepared roles state) : tree.dictionary.root = tree.root := by
  cases tree; rfl

theorem dictionaries_map (children : List (Prepared roles state)) :
    dictionaries children = children.map Prepared.dictionary := by
  induction children with
  | nil => rfl
  | cons first rest ih => simp only [dictionaries, List.map_cons, ih]

theorem dictionaries_roots (children : List (Prepared roles state)) :
    (dictionaries children).map Dictionary.root = children.map Prepared.root := by
  rw [dictionaries_map, List.map_map]
  apply List.map_congr_left
  intro tree _
  exact dictionary_root tree

theorem childItems_member (children : List (Prepared roles state)) (child : Prepared roles state)
    (present : child ∈ children) (item : Item roles state) (member : item ∈ child.items) :
    item ∈ childItems children := by
  induction children with
  | nil => cases present
  | cons first rest ih =>
      rcases List.mem_cons.mp present with rfl | tail
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ (ih tail)

/-- Independent local plan/term certificates. No stored-equation certificate is
part of this judgment; the transaction constructs it afterward. -/
inductive Valid (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (terms : TermInstances registry.roles state) :
    Prepared registry.roles state → Prop where
  | node {root : Occurrence registry.roles} {key : Nat}
      {located : Located state root.demand} {children : List (Prepared registry.roles state)}
      (plan : Plan registry checked (frames root) root key (children.map Prepared.root))
      (interpreted : terms root key located)
      (childrenValid : ∀ child ∈ children, Valid registry checked frames terms child) :
      Valid registry checked frames terms (.node root key located children)

/-- No interpretation is rerun at a changed state. Every original term and its
source identities are carried forward exactly. -/
def LiftedTerms (items : List (Item roles state)) (terms : TermInstances roles state) :
    TermInstances roles (record items) :=
  fun root key located => ∃ original, terms root key original ∧ located = relocate items original

/-- A single computed batch supplies every node. The subset form permits the
same theorem to apply to all subtrees without constructing separate states. -/
theorem valid_stored_in (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (terms : TermInstances registry.roles state)
    (tree : Prepared registry.roles state) (valid : Valid registry checked frames terms tree)
    (items : List (Item registry.roles state))
    (included : ∀ item ∈ tree.items, item ∈ items) :
    Evidence (StoredInstance (PlannedAt registry checked frames (LiftedTerms items terms))) tree.dictionary := by
  induction valid with
  | @node root key located children plan interpreted childrenValid ih =>
      apply Evidence.node
      · refine ⟨relocate items located, ⟨?_, ⟨located, interpreted, rfl⟩⟩, ?_⟩
        · simpa only [dictionaries_roots] using plan
        · exact GeneralDictionaryBatchRecording.batch_recorded items ⟨root.demand, located⟩
            (included _ (List.mem_cons_self))
      · intro dictionary member
        rw [dictionaries_map] at member
        obtain ⟨child, present, rfl⟩ := List.mem_map.mp member
        apply ih child present
        intro item member
        exact included item (List.mem_cons_of_mem _ (childItems_member children child present item member))

theorem transaction_stored (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (terms : TermInstances registry.roles state)
    (tree : Prepared registry.roles state) (valid : Valid registry checked frames terms tree) :
    Evidence (StoredInstance (PlannedAt registry checked frames (LiftedTerms tree.items terms))) tree.dictionary :=
  valid_stored_in registry checked frames terms tree valid tree.items (fun _ member => member)

/-- All nodes share each arbitrary model of the one transaction state. The
source dictionary witness is fixed before quantification over models. -/
theorem transaction_uniform (registry : Registry) (checked : Checked registry)
    (frames : Frames registry.roles) (terms : TermInstances registry.roles state)
    (tree : Prepared registry.roles state) (valid : Valid registry checked frames terms tree) :
    ∃ witness, Readback tree.root (erase tree.dictionary) witness ∧
      ∀ assignment, Models (record tree.items) assignment →
        Evidence (ModelInstance (PlannedAt registry checked frames (LiftedTerms tree.items terms)) assignment) witness := by
  refine ⟨tree.dictionary, ⟨dictionary_root tree, rfl⟩, ?_⟩
  intro assignment model
  exact indexed_all_models _ _ (transaction_stored registry checked frames terms tree valid) assignment model

/-- Exact joint feasibility, not a claim that arbitrary prepared dictionaries
have a model or that incompatible sibling equations can be accepted. -/
theorem transaction_models (tree : Prepared roles state) (assignment : Assignment) :
    Models (record tree.items) assignment ↔ Models state assignment ∧
      ∀ item ∈ tree.items, item.located.equations.Holds assignment :=
  GeneralDictionaryBatchRecording.batch_models tree.items assignment

end Yulang.GeneralDictionaryTransactions
