import Yulang.GeneralDictionarySource168Transport
import Yulang.GeneralDictionaryTreeTransport

/-! Whole finite source witnesses survive source-preserving relocation when
computed reports and schemas agree at their own node footprint. Unrelated
occurrences need not have matching inspections. Target state models and Metadata
remain explicit; arbitrary refresh is not claimed. -/
namespace Yulang.GeneralDictionaryRecursive168Transport
open GeneralDeclarations GeneralNominalRecursiveCandidates
open GeneralNominalReportSourceTransport GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries
open GeneralDictionarySource168Transport
variable {roles : Roles.RoleDecls}

def RelocatesAt (registry : Registry) (before after : Context)
    (slots : Fin before.state.base.slots → Fin after.state.base.slots)
    (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration (checked : DeclarationChecked registry.constructors roles declaration) bounds,
    declaration ∈ registry.declarations → declaration.id = key →
    arguments before root = some bounds → Finished (report before declaration bounds) →
    ∃ next, arguments after root = some next ∧
      report after declaration next = moveReport slots (report before declaration bounds) ∧
      generated registry after root declaration checked next = generated registry before root declaration checked bounds

theorem children_seed (before after : GeneralNominalState.State)
    (seed : after.seed = before.seed) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bs : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.children after registry root declaration checked bs =
      GeneralNominalAllocation.children before registry root declaration checked bs := by
  have alloc : ∀ key, @GeneralNominalAllocation.allocation roles after registry root.identity key =
      @GeneralNominalAllocation.allocation roles before registry root.identity key := by
    intro key
    funext clause
    simp only [GeneralNominalAllocation.allocation,GeneralNominalAllocation.source,seed]
  simp only [GeneralNominalAllocation.children,GeneralNominalAllocation.frame,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.source,seed,alloc]

theorem instance_relocated (registry : Registry) (before after : Context)
    (slots : Fin before.state.base.slots → Fin after.state.base.slots)
    (sources : ∀ slot, after.state.base.source (slots slot) = before.state.base.source slot)
    (seed : after.state.seed = before.state.seed) (metadata : Metadata registry after)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : RelocatesAt registry before after slots root key)
    (model : Assignment) (current : GeneralNominalState.Models after.state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,_,branch⟩ := old
  obtain ⟨next,found,reports,schemas⟩ := same declaration checked bounds visible identity located finished
  have bs : bindings after.state (report after declaration next) = bindings before.state (report before declaration bounds) := by
    rw [reports]; exact bindings_preserved slots sources _
  refine ⟨declaration,visible,checked,identity,role,next,found,?_,?_,?_,metadata,?_⟩
  · rw [reports]; exact (finished_iff slots _).mpr finished
  · exact ⟨ready.1,by rw [schemas]; exact ready.2⟩
  · rw [bs,children_seed before.state after.state seed]
    exact emitted
  · exact branch_relocated registry before after root declaration checked bounds next slots sources seed reports schemas model current branch

def RelocatesTree (registry : Registry) (before after : Context)
    (slots : Fin before.state.base.slots → Fin after.state.base.slots)
    (tree : Dictionary roles) : Prop :=
  ∀ occurrence key, (occurrence,key) ∈ observations tree → RelocatesAt registry before after slots occurrence key

theorem indexed_relocated (registry : Registry) (before after : Context)
    (slots : Fin before.state.base.slots → Fin after.state.base.slots)
    (sources : ∀ slot, after.state.base.source (slots slot) = before.state.base.source slot)
    (seed : after.state.seed = before.state.seed) (metadata : Metadata registry after)
    (model : Assignment) (current : GeneralNominalState.Models after.state model)
    (tree : Dictionary roles)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry before model) tree)
    (same : RelocatesTree registry before after slots tree) :
    Evidence (GeneralDictionaryRecursiveEvidence.Instance registry after model) tree := by
  induction old with
  | @node occurrence key children localRule given ih =>
    refine .node (instance_relocated registry before after slots sources seed metadata occurrence key _
      (same occurrence key List.mem_cons_self) model current localRule) ?_
    intro child member
    apply ih child member
    intro demand selected present
    exact same demand selected (List.mem_cons_of_mem _
      (GeneralDictionaryTreeTransport.child_observation children child member _ present))

theorem erased_relocated (registry : Registry) (before after : Context)
    (slots : Fin before.state.base.slots → Fin after.state.base.slots)
    (sources : ∀ slot, after.state.base.source (slots slot) = before.state.base.source slot)
    (seed : after.state.seed = before.state.seed) (metadata : Metadata registry after)
    (model : Assignment) (current : GeneralNominalState.Models after.state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (tree : Dictionary roles) (readback : Readback root payload tree)
    (old : Evidence (GeneralDictionaryRecursiveEvidence.Instance registry before model) tree)
    (same : RelocatesTree registry before after slots tree) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after model root payload :=
  ⟨tree,readback,indexed_relocated registry before after slots sources seed metadata model current tree old same⟩

end Yulang.GeneralDictionaryRecursive168Transport
