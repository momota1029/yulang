import Yulang.GeneralSourceDictionaries

/-!
# Exact evidence readback between source-indexed and runtime dictionaries

The independent judgment below relates a real source occurrence to the existing
key-only runtime payload. It retains all children, in order and with multiplicity.
Its equivalence with indexed Evidence supplies a missing representation adapter;
local declaration-instance semantics remains an explicit parameter.
-/
namespace Yulang.GeneralDictionaryReadback
open GeneralSourceDictionaries
open CommonRoleOutermostResolver (All₂)
abbrev Payload := CommonRoleOutermostResolver.Dictionary

/-- Independent recursive evidence, not a predicate on an executor's result. -/
inductive PayloadEvidence (localRule : LocalInstance roles) :
    Occurrence roles → Payload → Prop where
  | node (instanceRule : localRule occurrence key children)
      (allChildren : All₂ (PayloadEvidence localRule) children dictionaries) :
      PayloadEvidence localRule occurrence (.node key dictionaries)

/-- Exact ordered correspondence, including repeated source occurrences. -/
theorem children_payload (localRule : LocalInstance roles)
    (children : List (Dictionary roles))
    (given : ∀ child ∈ children, PayloadEvidence localRule child.root (erase child)) :
    All₂ (PayloadEvidence localRule) (children.map Dictionary.root) (eraseChildren children) := by
  induction children with
  | nil => exact .nil
  | cons first rest ih =>
      exact .cons (given first (by simp))
        (ih (fun child member => given child (List.mem_cons_of_mem _ member)))

theorem indexed_to_payload (localRule : LocalInstance roles) (tree : Dictionary roles)
    (given : Evidence localRule tree) : PayloadEvidence localRule tree.root (erase tree) := by
  induction given with
  | node instanceRule children ih => exact .node instanceRule (children_payload _ _ ih)

mutual
  theorem payload_to_indexed (localRule : LocalInstance roles) (payload : Payload)
      (occurrence : Occurrence roles) (given : PayloadEvidence localRule occurrence payload) :
      ∃ tree, Readback occurrence payload tree ∧ Evidence localRule tree := by
    cases payload with
    | node key dictionaries =>
        cases given with
        | node instanceRule allChildren =>
            obtain ⟨trees, roots, erased, evidence⟩ :=
              payloads_to_indexed localRule dictionaries _ allChildren
            refine ⟨.node occurrence key trees, ⟨rfl, ?_⟩, .node ?_ evidence⟩
            · simp only [erase, erased]
            · rw [roots]
              exact instanceRule
    termination_by sizeOf payload

  theorem payloads_to_indexed (localRule : LocalInstance roles) (payloads : List Payload)
      (occurrences : List (Occurrence roles))
      (given : All₂ (PayloadEvidence localRule) occurrences payloads) :
      ∃ trees : List (Dictionary roles), trees.map Dictionary.root = occurrences ∧
        eraseChildren trees = payloads ∧ ∀ tree ∈ trees, Evidence localRule tree := by
    cases given with
    | nil => exact ⟨[], rfl, rfl, by simp⟩
    | @cons occurrence payload occurrences payloads first rest =>
        obtain ⟨tree, ⟨root, erased⟩, evidence⟩ := payload_to_indexed localRule payload occurrence first
        obtain ⟨trees, roots, erasures, evidences⟩ :=
          payloads_to_indexed localRule payloads occurrences rest
        refine ⟨tree :: trees, ?_, ?_, ?_⟩
        · simp only [List.map_cons, root, roots]
        · simp only [eraseChildren, erased, erasures]
        · intro child member
          rcases List.mem_cons.mp member with rfl | member
          · exact evidence
          · exact evidences child member
    termination_by sizeOf payloads
end

/-- No hidden source-identity or child-existence premise: the witness is reconstructed
from the independent recursive derivation, not guessed from its erased keys. -/
theorem payload_iff_erased (localRule : LocalInstance roles) (occurrence : Occurrence roles)
    (payload : Payload) :
    PayloadEvidence localRule occurrence payload ↔ ErasedEvidence localRule occurrence payload := by
  constructor
  · exact payload_to_indexed localRule payload occurrence
  · rintro ⟨tree, ⟨root, erased⟩, evidence⟩
    simpa only [root, erased] using indexed_to_payload localRule tree evidence

/-- A precise node introduction adapter for a key-only B4 Evidence implementation.
The localRule premise remains a real, separate declaration/candidate obligation. -/
theorem erased_evidence_node (localRule : LocalInstance roles) (occurrence : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) (dictionaries : List Payload)
    (instanceRule : localRule occurrence key children)
    (given : All₂ (ErasedEvidence localRule) children dictionaries) :
    ErasedEvidence localRule occurrence (.node key dictionaries) := by
  apply (payload_iff_erased localRule occurrence _).mp
  have convert : ∀ {cs ds}, All₂ (ErasedEvidence localRule) cs ds →
      All₂ (PayloadEvidence localRule) cs ds := by
    intro cs ds h
    induction h with
    | nil => exact .nil
    | cons first rest ih => exact .cons ((payload_iff_erased _ _ _).mpr first) ih
  exact .node instanceRule (convert given)

/-- Determinism of source obligations is supplied by actual declaration instances,
not by equality of erased payloads. No freshness or allocator rule is invented. -/
def ChildrenFunctional (localRule : LocalInstance roles) : Prop :=
  ∀ occurrence key first last, localRule occurrence key first →
    localRule occurrence key last → first = last

mutual
  /-- Erasure becomes injective on valid evidence with a fixed source occurrence
  only when the concrete local-instance relation has deterministic children. -/
  theorem indexed_unique (localRule : LocalInstance roles) (functional : ChildrenFunctional localRule)
      (first last : Dictionary roles) (sameRoot : first.root = last.root)
      (samePayload : erase first = erase last)
      (firstEvidence : Evidence localRule first) (lastEvidence : Evidence localRule last) :
      first = last := by
    cases first with
    | node occurrence key children =>
        cases last with
        | node other otherKey others =>
            change occurrence = other at sameRoot
            subst other
            change CommonRoleOutermostResolver.Dictionary.node key (eraseChildren children) =
              CommonRoleOutermostResolver.Dictionary.node otherKey (eraseChildren others) at samePayload
            have keys := CommonRoleOutermostResolver.Dictionary.node.inj samePayload
            cases keys.1
            obtain ⟨firstRule, firstChildren⟩ := (evidence_node_iff ..).mp firstEvidence
            obtain ⟨lastRule, lastChildren⟩ := (evidence_node_iff ..).mp lastEvidence
            have roots := functional occurrence key _ _ firstRule lastRule
            have same := indexed_children_unique localRule functional children others roots keys.2
              firstChildren lastChildren
            cases same
            rfl
    termination_by sizeOf first

  theorem indexed_children_unique (localRule : LocalInstance roles) (functional : ChildrenFunctional localRule)
      (first last : List (Dictionary roles))
      (roots : first.map Dictionary.root = last.map Dictionary.root)
      (payloads : eraseChildren first = eraseChildren last)
      (firstEvidence : ∀ tree ∈ first, Evidence localRule tree)
      (lastEvidence : ∀ tree ∈ last, Evidence localRule tree) : first = last := by
    cases first with
    | nil => cases last with
      | nil => rfl
      | cons tree rest => cases roots
    | cons tree rest =>
        cases last with
        | nil => cases roots
        | cons other others =>
            have roots' := List.cons.inj roots
            have payloads' := List.cons.inj payloads
            have same := indexed_unique localRule functional tree other roots'.1 payloads'.1
              (firstEvidence tree (by simp)) (lastEvidence other (by simp))
            have tails := indexed_children_unique localRule functional rest others roots'.2 payloads'.2
              (fun t h => firstEvidence t (List.mem_cons_of_mem _ h))
              (fun t h => lastEvidence t (List.mem_cons_of_mem _ h))
            cases same
            cases tails
            rfl
    termination_by sizeOf first
end

/-- Existence plus uniqueness of the complete source-indexed witness, when the
local declaration instance has deterministic children. -/
theorem payload_unique_readback (localRule : LocalInstance roles)
    (functional : ChildrenFunctional localRule) (occurrence : Occurrence roles) (payload : Payload)
    (given : PayloadEvidence localRule occurrence payload) :
    ∃ tree, (Readback occurrence payload tree ∧ Evidence localRule tree) ∧
      ∀ other, Readback occurrence payload other → Evidence localRule other → other = tree := by
  obtain ⟨tree, readback, evidence⟩ := payload_to_indexed localRule payload occurrence given
  refine ⟨tree, ⟨readback, evidence⟩, ?_⟩
  intro other otherReadback otherEvidence
  exact indexed_unique localRule functional other tree
    (otherReadback.1.trans readback.1.symm) (otherReadback.2.trans readback.2.symm) otherEvidence evidence

end Yulang.GeneralDictionaryReadback
