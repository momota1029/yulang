import Yulang.GeneralNominalActiveSupport249
/-! Actual propagation with owner slots separated from actual model reads and
binding endpoints, rather than from every reservation. Sufficient protection
is explicit; source eligibility and complete metadata privacy are not inferred. -/
namespace Yulang.GeneralNominalActiveMerge249
open GeneralDeclarations GeneralNominalAllocation
open GeneralNominalState GeneralNominalCommonBridge
open GeneralNominalActiveSupport249

def endpointSources (bindings : Bindings) : List Nat :=
 bindings.flatMap fun binding => [binding.2.1,binding.2.2]

def protectedSources (state : State) (bindings : Bindings) (extra : List Nat) : List Nat :=
 activeSources state ++ endpointSources bindings ++ extra

theorem endpoints_covered (state : State) (bindings : Bindings) (extra : List Nat) :
 GeneralNominalAllocationSupport.Endpoints bindings (protectedSources state bindings extra) := by
 intro binding member
 constructor
 · exact List.mem_append_left _ (List.mem_append_right _
     (List.mem_flatMap.mpr ⟨binding,member,by simp⟩))
 · exact List.mem_append_left _ (List.mem_append_right _
     (List.mem_flatMap.mpr ⟨binding,member,by simp⟩))

theorem active_covered (state : State) (bindings : Bindings) (extra : List Nat) :
 activeSources state ⊆ protectedSources state bindings extra :=
 fun _ member => List.mem_append_left _ (List.mem_append_left _ member)

theorem extra_covered (state : State) (bindings : Bindings) (extra : List Nat) :
 extra ⊆ protectedSources state bindings extra := fun _ member => List.mem_append_right _ member

theorem propagation_model (state : State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (bindings : Bindings) (extra : List Nat)
 (protectedPool : GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id bindings declaration.inputNames
   (protectedSources state bindings extra))
 (assignment : Assignment) (valid : Models state assignment) (cross : Compatible bindings assignment) :
 ∃ extended, Models (propagate state registry root declaration bindings) extended ∧
  (∀ name ∈ activeSources state, extended name = assignment name) ∧
  (∀ name ∈ extra, extended name = assignment name) ∧
  (∀ name, (extended name).2 = (assignment name).2) := by
 obtain ⟨extended,merges,kept,rows⟩ := GeneralNominalOrderedMerge248.actual_merge_extension
   state registry root declaration bindings (protectedSources state bindings extra) protectedPool
   (endpoints_covered state bindings extra) assignment
 have active : ∀ name ∈ activeSources state, extended name = assignment name :=
   fun name member => kept name (active_covered state bindings extra member)
 refine ⟨extended,?_,active,(fun name member => kept name (extra_covered state bindings extra member)),rows⟩
 apply (propagate_models state registry root declaration bindings extended).mpr
 refine ⟨models_of_agrees state assignment extended (fun name member => (active name member).symm) valid,?_,merges⟩
 intro first one last two same
 change CommonNominalFullCarrier.Subtype (extended first.2.1).1 (extended last.2.2).1
 rw [kept first.2.1 ((endpoints_covered state bindings extra first one).1),
   kept last.2.2 ((endpoints_covered state bindings extra last two).2)]
 exact cross first one last two same
theorem reservations_irrelevant (state : State) (reserved : List Nat) (bindings : Bindings) (extra : List Nat) :
 protectedSources {state with reserved := reserved} bindings extra = protectedSources state bindings extra := rfl

theorem allocated_irrelevant (state : State) (allocated : List GeneralNominalIdentities.Origin) (bindings : Bindings) (extra : List Nat) :
 protectedSources {state with allocated := allocated} bindings extra = protectedSources state bindings extra := rfl

theorem protected_of_bounded (state : State) (root : Nat) (declaration : Declaration)
 (bindings : Bindings) (extra : List Nat)
 (bounded : ∀ name ∈ protectedSources state bindings extra, name ≤ state.seed) :
 GeneralNominalRebaseDefinitions241.Fresh state.seed root declaration.id bindings declaration.inputNames
   (protectedSources state bindings extra) := by
 intro name _ _
 constructor
 · intro member
   have above := GeneralNominalIdentities.source_above_seed state.seed
     (origin root declaration.id 0 name 0)
   exact (Nat.not_le_of_gt above) (bounded _ member)
 · intro member
   have above := GeneralNominalIdentities.source_above_seed state.seed
     (origin root declaration.id 1 name 0)
   exact (Nat.not_le_of_gt above) (bounded _ member)

theorem bounded_propagation (state : State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (bindings : Bindings) (extra : List Nat)
 (bounded : ∀ name ∈ protectedSources state bindings extra, name ≤ state.seed)
 (assignment : Assignment) (valid : Models state assignment) (cross : Compatible bindings assignment) :
 ∃ extended, Models (propagate state registry root declaration bindings) extended ∧
  (∀ name ∈ activeSources state, extended name = assignment name) ∧
  (∀ name ∈ extra, extended name = assignment name) ∧
  (∀ name, (extended name).2 = (assignment name).2) :=
 propagation_model state registry root declaration bindings extra
   (protected_of_bounded state root declaration bindings extra bounded) assignment valid cross
end Yulang.GeneralNominalActiveMerge249
