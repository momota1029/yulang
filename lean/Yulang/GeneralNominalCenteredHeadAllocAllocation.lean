import Yulang.GeneralNominalCenteredHeadAllocEncoding

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocAllocation
open GeneralDeclarations GeneralSourceDictionaries GeneralDeclarationDemands
open GeneralNominalCenteredHeadAllocEncoding
open GeneralNominalAllocation (origin source)

/-- The pair is an injective encoding of both local source identities. -/
def outputKey (invocation key clause equation : Nat) : GeneralNominalIdentities.Origin :=
  origin invocation key 5 (GeneralNominalIdentities.pair clause equation) 0

def declarationKeys (invocation : Nat) (value : Declaration) : List GeneralNominalIdentities.Origin :=
  GeneralNominalAllocation.declarationKeys invocation (declaration value)

def keys (value : Registry) (invocation : Nat) : List GeneralNominalIdentities.Origin :=
  value.declarations.flatMap (declarationKeys invocation)

def reserved (state : GeneralNominalState.State) (value : Registry) (invocation : Nat) : List Nat :=
  (keys value invocation).map (source state value invocation)

def allocation (state : GeneralNominalState.State) (value : Registry) (invocation key : Nat)
    (parent : Clause) : Allocation roles parent where
  arguments := (GeneralNominalAllocation.allocation state value invocation key parent).arguments
  outputs := fun identity => source state value invocation (outputKey invocation key parent.id identity)

theorem keys_exact : keys value invocation = GeneralNominalAllocation.keys (registry value) invocation := by
  simp only [keys,GeneralNominalAllocation.keys,registry,List.flatMap_map]
  rfl

theorem reserved_exact : reserved state value invocation =
    GeneralNominalAllocation.reserved state (registry value) invocation := by
  rw [reserved,keys_exact]
  rfl

theorem output_identity :
    (allocation (roles := roles) state value invocation key first).outputs a =
      (allocation (roles := roles) state value invocation key last).outputs b ↔ first.id = last.id ∧ a = b := by
  change GeneralNominalIdentities.source state.seed (outputKey invocation key first.id a) =
    GeneralNominalIdentities.source state.seed (outputKey invocation key last.id b) ↔ _
  rw [GeneralNominalIdentities.source_identity]
  simp only [outputKey,origin,Prod.mk.injEq,true_and,and_true,equation_key]

theorem output_reserved (visible : d ∈ value.declarations) (present : c ∈ d.requirements)
    (within : e ∈ c.outputs) :
    (allocation (roles := roles) state value invocation d.id c).outputs e.id ∈ reserved state value invocation := by
  apply List.mem_map.mpr
  refine ⟨outputKey invocation d.id c.id e.id,?_,rfl⟩
  apply List.mem_flatMap.mpr
  refine ⟨d,visible,?_⟩
  unfold declarationKeys GeneralNominalAllocation.declarationKeys
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨clause c,List.mem_map.mpr ⟨c,present,rfl⟩,?_⟩
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨equation c.id e,List.mem_map.mpr ⟨e,within,rfl⟩,rfl⟩

theorem capture_unchanged (state : GeneralNominalState.State) (value : Registry) (invocation : Nat)
    (d : Declaration) (bindings) :
    GeneralNominalAllocation.capture state (registry value) invocation (declaration d).id bindings =
      GeneralNominalAllocation.capture state value invocation d.id bindings := rfl

theorem compiled_output_target (state : GeneralNominalState.State) (value : Registry) (invocation : Nat)
    (d : Declaration) (c : Clause) (capture : Capture) (e : Equation) :
    outputTarget (declaration d) capture
        (GeneralNominalAllocation.allocation (roles := roles) state (registry value) invocation d.id (clause c)).outputs
        (equation c.id e) =
      outputTarget d capture (allocation (roles := roles) state value invocation d.id c).outputs e := by
  unfold outputTarget
  simp only [equation,outputNames]
  split <;> rfl

theorem shared_binder_unchanged (state : GeneralNominalState.State) (value : Registry) (invocation : Nat)
    (d : Declaration) (c : Clause) (capture : Capture) (e : Equation)
    (named : name ∈ d.outputNames) (rhs : e.rhs = .var name) :
    outputTarget (declaration d) capture
        (GeneralNominalAllocation.allocation (roles := roles) state (registry value) invocation d.id (clause c)).outputs
        (equation c.id e) = capture.outputs name := by
  rw [compiled_output_target]
  exact generated_output_target d capture _ e name named rhs

theorem child_demand (state : GeneralNominalState.State) (value : Registry) (invocation : Nat)
    (d : Declaration) (c : Clause) (valid : c.Signature roles) (capture : Capture) :
    childDemand (declaration d) (clause c) (clause_signature valid) capture
      (GeneralNominalAllocation.allocation state (registry value) invocation d.id (clause c)) =
    childDemand d c valid capture (allocation state value invocation d.id c) := by
  unfold childDemand
  congr 1
  simp only [clause,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro e member
  exact congrArg (fun target => (⟨e.name,target⟩ : GeneralSourceState.Output))
    (compiled_output_target state value invocation d c capture e)

end Yulang.GeneralNominalCenteredHeadAllocAllocation
