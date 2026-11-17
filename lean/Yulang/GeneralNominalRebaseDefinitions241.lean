import Yulang.GeneralNominalFiniteEquationRealization236
import Yulang.GeneralNominalVersionedAllocation231
import Yulang.GeneralNominalAllocationSupport
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRebaseDefinitions241
open GeneralNominalAllocation (Bindings occurrences lower upper)
/-! Stable owner-local merge definitions with an explicit protected support.
This module re-evaluates the real legacy capture/merge formulas. It does not
claim that allocation ownership supplies semantic privacy or a new boundary. -/
def slot (seed root declaration purpose name : Nat) (_bindings : GeneralNominalAllocation.Bindings) : Nat :=
 GeneralNominalIdentities.source seed (GeneralNominalAllocation.origin root declaration purpose name 0)

theorem slot_stable : slot seed root declaration purpose name first =
 slot seed root declaration purpose name last := rfl
open GeneralNominalFiniteEquationRealization236 (Entry)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (TyTerm)
variable (seed root declaration : Nat) (bindings : Bindings) (names : List Nat)

def entries : List Entry := names.flatMap fun name =>
  if (occurrences bindings name).length = 1 then [] else
    [(slot seed root declaration 0 name bindings,lower (occurrences bindings name)),
     (slot seed root declaration 1 name bindings,upper (occurrences bindings name))]

theorem member_iff : entry ∈ entries seed root declaration bindings names ↔
    ∃ name ∈ names, (occurrences bindings name).length ≠ 1 ∧
      (entry = (slot seed root declaration 0 name bindings,lower (occurrences bindings name)) ∨
       entry = (slot seed root declaration 1 name bindings,upper (occurrences bindings name))) := by
  unfold entries
  constructor
  · intro member
    obtain ⟨name,named,member⟩ := List.mem_flatMap.mp member
    split at member
    · cases member
    · exact ⟨name,named,by assumption,by simpa using member⟩
  · rintro ⟨name,named,many,member⟩
    exact List.mem_flatMap.mpr ⟨name,named,by simp only [many,ite_false]; simpa using member⟩

theorem slot_names {p q a b : Nat}
    (same : slot seed root declaration p a bindings = slot seed root declaration q b bindings) : p=q ∧ a=b := by
  have equal := (GeneralNominalIdentities.source_identity seed _ _).mp same
  exact ⟨congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.1) equal,
    congrArg (fun k : GeneralNominalIdentities.Origin => k.2.2.2.1) equal⟩

theorem coherent : ∀ first ∈ entries seed root declaration bindings names,
    ∀ last ∈ entries seed root declaration bindings names, first.1 = last.1 → first.2 = last.2 := by
  intro first one last two equal
  obtain ⟨a,_,_,one⟩ := (member_iff seed root declaration bindings names).mp one
  obtain ⟨b,_,_,two⟩ := (member_iff seed root declaration bindings names).mp two
  rcases one with rfl | rfl <;> rcases two with rfl | rfl
  all_goals have same := slot_names seed root declaration bindings equal
  · rw [same.2]
  · cases same.1
  · cases same.1
  · rw [same.2]

def Fresh (pool : List Nat) : Prop := ∀ name ∈ names, (occurrences bindings name).length ≠ 1 →
  slot seed root declaration 0 name bindings ∉ pool ∧ slot seed root declaration 1 name bindings ∉ pool

theorem entries_fresh (fresh : Fresh seed root declaration bindings names pool) :
    ∀ entry ∈ entries seed root declaration bindings names, entry.1 ∉ pool := by
  intro entry member
  obtain ⟨name,named,many,rfl | rfl⟩ := (member_iff seed root declaration bindings names).mp member
  · exact (fresh name named many).1
  · exact (fresh name named many).2

theorem supported (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) :
    ∀ entry ∈ entries seed root declaration bindings names,
      ∀ identity ∈ GeneralNominalState.typeSources entry.2, identity ∈ pool := by
  intro entry member
  obtain ⟨name,_,_,rfl | rfl⟩ := (member_iff seed root declaration bindings names).mp member
  · exact GeneralNominalAllocationSupport.lower_sources _ (GeneralNominalAllocationSupport.occurrences_endpoints linked name)
  · exact GeneralNominalAllocationSupport.upper_sources _ (GeneralNominalAllocationSupport.occurrences_endpoints linked name)

noncomputable def patch (model : Assignment) : Assignment :=
  GeneralNominalFiniteEquationRealization236.patch (entries seed root declaration bindings names) model

theorem preserves (fresh : Fresh seed root declaration bindings names pool) :
    ∀ identity ∈ pool, patch seed root declaration bindings names model identity = model identity :=
  GeneralNominalFiniteEquationRealization236.preserves _ (entries_fresh seed root declaration bindings names fresh)

theorem equations (fresh : Fresh seed root declaration bindings names pool)
    (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) :
    ∀ entry ∈ entries seed root declaration bindings names,
      PresenceNormalForm.All CommonNominalFullCarrier.model (patch seed root declaration bindings names model)
        (GeneralNominalAllocation.equations entry.1 entry.2) :=
  GeneralNominalFiniteEquationRealization236.equations _ (coherent seed root declaration bindings names)
    (entries_fresh seed root declaration bindings names fresh) (supported seed root declaration bindings names linked)

theorem merges (state : GeneralNominalState.State) (registry : GeneralDeclarations.Registry)
    (root : Nat) (declaration : GeneralDeclarations.Declaration) (bindings : Bindings) (model : Assignment)
    (fresh : Fresh state.seed root declaration.id bindings declaration.inputNames pool)
    (linked : GeneralNominalAllocationSupport.Endpoints bindings pool) :
    PresenceNormalForm.All CommonNominalFullCarrier.model
      (patch state.seed root declaration.id bindings declaration.inputNames model)
      (GeneralNominalAllocation.merges state registry root declaration bindings) := by
  intro atom member
  obtain ⟨name,named,member⟩ := List.mem_flatMap.mp member
  have produce (many : (occurrences bindings name).length ≠ 1) :
      PresenceNormalForm.All CommonNominalFullCarrier.model
        (patch state.seed root declaration.id bindings declaration.inputNames model)
        (GeneralNominalAllocation.equations (slot state.seed root declaration.id 0 name bindings) (lower (occurrences bindings name)) ++
         GeneralNominalAllocation.equations (slot state.seed root declaration.id 1 name bindings) (upper (occurrences bindings name))) := by
    apply (PresenceNormalForm.all_append ..).mpr
    constructor
    · exact equations state.seed root declaration.id bindings declaration.inputNames fresh linked _
        ((member_iff ..).mpr ⟨name,named,many,Or.inl rfl⟩)
    · exact equations state.seed root declaration.id bindings declaration.inputNames fresh linked _
        ((member_iff ..).mpr ⟨name,named,many,Or.inr rfl⟩)
  cases found : occurrences bindings name with
  | nil => exact produce (by simp [found]) atom (by simpa [found,GeneralNominalAllocation.capture,GeneralNominalAllocation.source,slot] using member)
  | cons first rest =>
    cases rest with
    | nil => simp [found] at member
    | cons second tail => exact produce (by simp [found]) atom (by simpa [found,GeneralNominalAllocation.capture,GeneralNominalAllocation.source,slot] using member)
end Yulang.GeneralNominalRebaseDefinitions241
