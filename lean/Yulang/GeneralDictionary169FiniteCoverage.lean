import Yulang.GeneralDictionaryMixed168Tree

/-! Local structural coverage and accessibility of chosen children construct
one finite mixed dictionary, uniformly for all current models. Accessibility
and coverage remain explicit obligations, not new V5 boundary assumptions. -/
namespace Yulang.GeneralDictionary169FiniteCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryReadback
open CommonRoleOutermostResolver (All₂)
open GeneralDictionaryMixed168Tree (MixedTree)
variable {roles : Roles.RoleDecls}

/-- One node only. No child trees, Instance, or semantic Evidence occur here. -/
inductive Node (registry : Registry) (state : Tracked roles) : Occurrence roles → Type
  | recorded (packet : Packet roles) (member : packet ∈ state.current.packets)
      (relocation : GeneralDictionaryRecorded168Relocation.Relocates registry state packet) :
      Node registry state packet.site.occurrence
  | scalar (occurrence : Occurrence roles) (declaration : Declaration)
      (visible : declaration ∈ registry.declarations)
      (checked : DeclarationChecked registry.constructors roles declaration)
      (shape : GeneralDictionaryScalarLeaf.ScalarLeafShape state.current.context occurrence declaration) :
      Node registry state occurrence
  | spine (occurrence : Occurrence roles) (declaration : Declaration)
      (visible : declaration ∈ registry.declarations)
      (checked : DeclarationChecked registry.constructors roles declaration)
      (shape : GeneralDictionarySpineLeaf.SpineLeafShape state.current.context occurrence declaration) :
      Node registry state occurrence

def Node.children {registry : Registry} {state : Tracked roles} {occurrence : Occurrence roles} : Node registry state occurrence → List (Occurrence roles)
  | .recorded packet _ _ => packet.children
  | .scalar .. => []
  | .spine .. => []

def Node.key {registry : Registry} {state : Tracked roles} {occurrence : Occurrence roles} : Node registry state occurrence → Nat
  | .recorded packet _ _ => packet.declaration.id
  | .scalar _ declaration .. => declaration.id
  | .spine _ declaration .. => declaration.id

theorem node_tree (node : Node registry state occurrence) (payloads : List Payload)
    (children : All₂ (MixedTree registry state) node.children payloads) :
    MixedTree registry state occurrence (.node node.key payloads) := by
  cases node with
  | recorded packet member relocation => exact .recorded packet member relocation payloads children
  | scalar occurrence declaration visible checked shape =>
    cases children
    exact .scalar occurrence declaration visible checked shape
  | spine occurrence declaration visible checked shape =>
    cases children
    exact .spine occurrence declaration visible checked shape

/-- Coverage is only required on the chosen child-closed domain, not on all
language occurrences or all generated requests. -/
structure Coverage (registry : Registry) (state : Tracked roles) (domain : Occurrence roles → Prop) where
  node : ∀ occurrence, domain occurrence → Node registry state occurrence
  closed : ∀ occurrence member child, child ∈ (node occurrence member).children → domain child

def Child (coverage : Coverage registry state domain)
    (child parent : Subtype domain) : Prop :=
  child.val ∈ (coverage.node parent.val parent.property).children

private theorem collect (sites : List (Occurrence roles))
    (trees : ∀ child ∈ sites, ∃ payload, MixedTree registry state child payload) :
    ∃ payloads, All₂ (MixedTree registry state) sites payloads := by
  induction sites with
  | nil => exact ⟨[],.nil⟩
  | cons child rest ih =>
    obtain ⟨payload,one⟩ := trees child (by simp)
    obtain ⟨payloads,others⟩ := ih (fun next member => trees next (by simp [member]))
    exact ⟨payload :: payloads,.cons one others⟩

theorem accessible_tree (coverage : Coverage registry state domain) (root : Subtype domain)
    (accessible : Acc (Child coverage) root) :
    ∃ payload, MixedTree registry state root.val payload := by
  induction accessible with
  | intro current predecessors ih =>
    let node := coverage.node current.val current.property
    obtain ⟨payloads,children⟩ := collect node.children (fun child member =>
      ih ⟨child,coverage.closed current.val current.property child member⟩ member)
    exact ⟨.node node.key payloads,node_tree node payloads children⟩

theorem wellFounded_tree (coverage : Coverage registry state domain)
    (terminates : WellFounded (Child coverage)) (root : Subtype domain) :
    ∃ payload, MixedTree registry state root.val payload :=
  accessible_tree coverage root (terminates.apply root)

/-- The witness precedes the model quantifier: one payload works in every
current model. Neither satisfiability nor execution termination is concluded. -/
theorem uniform_dictionary (coverage : Coverage registry state domain) (focus : Subtype domain)
    (accessible : Acc (Child coverage) focus)
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state) :
    ∃ payload, MixedTree registry state focus.val payload ∧
      ∀ model, Models state.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus.val payload := by
  obtain ⟨payload,tree⟩ := accessible_tree coverage focus accessible
  exact ⟨payload,tree,fun model valid => GeneralDictionaryMixed168Tree.current_evidence formed tree model valid⟩
end Yulang.GeneralDictionary169FiniteCoverage
