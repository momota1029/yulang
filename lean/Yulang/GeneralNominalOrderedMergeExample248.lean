import Yulang.GeneralNominalOrderedMerge248
/-! Concrete actual lower/upper merge entries with a repeated input name.
No distinct-input-name assumption is needed. This regression instantiates the
real definitions, but is not a complete reachable-source execution trace. -/
namespace Yulang.GeneralNominalOrderedMergeExample248
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalAllocation (Bindings)
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedPrepared247

def bindings : Bindings := [(7,(0,1)),(7,(1,0))]
def names : List Nat := [7,7]
def pool : List Nat := [0,1]
def lo : Nat := GeneralNominalRebaseDefinitions241.slot 10 0 0 0 7 bindings
def hi : Nat := GeneralNominalRebaseDefinitions241.slot 10 0 0 1 7 bindings

theorem protected_pool : GeneralNominalRebaseDefinitions241.Fresh 10 0 0 bindings names pool := by
 intro name _ _
 constructor
 · have above := GeneralNominalIdentities.source_above_seed 10 (GeneralNominalAllocation.origin 0 0 0 name 0)
   intro collision
   simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at collision
   change 10 < GeneralNominalRebaseDefinitions241.slot 10 0 0 0 name bindings at above
   omega
 · have above := GeneralNominalIdentities.source_above_seed 10 (GeneralNominalAllocation.origin 0 0 1 name 0)
   intro collision
   simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at collision
   change 10 < GeneralNominalRebaseDefinitions241.slot 10 0 0 1 name bindings at above
   omega

theorem endpoints : GeneralNominalAllocationSupport.Endpoints bindings pool := by
 intro binding member
 simp only [bindings,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl <;> simp [pool]

theorem actual_entries : GeneralNominalRebaseDefinitions241.entries 10 0 0 bindings names =
 [(lo,TyTerm.union (.var 0) (.var 1)),(hi,TyTerm.inter (.var 1) (.var 0)),
  (lo,TyTerm.union (.var 0) (.var 1)),(hi,TyTerm.inter (.var 1) (.var 0))] := rfl

theorem repeated_input_prepares : ∃ sorted,
 prepare (GeneralNominalRebaseDefinitions241.entries 10 0 0 bindings names) = some sorted ∧ SafeOrder sorted :=
 GeneralNominalOrderedMerge248.prepared 10 0 0 bindings names pool protected_pool endpoints

theorem every_boundary_extends (assignment : GeneralNominalCommonBridge.Assignment) :
 ∃ sorted extended,
 prepare (GeneralNominalRebaseDefinitions241.entries 10 0 0 bindings names) = some sorted ∧
 extended = solve CommonNominalFullCarrier.model sorted assignment ∧
 All CommonNominalFullCarrier.model extended (block (GeneralNominalRebaseDefinitions241.entries 10 0 0 bindings names)) ∧
 (∀ name ∈ pool, extended name = assignment name) ∧ (∀ name, (extended name).2 = (assignment name).2) :=
 GeneralNominalOrderedMerge248.original_extension 10 0 0 bindings names pool protected_pool endpoints assignment
end Yulang.GeneralNominalOrderedMergeExample248
