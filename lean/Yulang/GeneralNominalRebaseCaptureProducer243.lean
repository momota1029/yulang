import Yulang.GeneralNominalRebaseEndpointProducer243
namespace Yulang.GeneralNominalRebaseCaptureProducer243
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalAllocationSupport
open GeneralNominalAllocation (capture occurrences)
open GeneralNominalRebaseSourceSteps243
open GeneralNominalRebaseStablePool243 (pool)

theorem capture_supported
 (supported : Endpoints bindings values)
 (reserved : GeneralNominalAllocation.reserved state registry invocation ⊆ values)
 (visible : declaration ∈ registry.declarations) (named : name ∈ declaration.inputNames) :
 ((capture state registry invocation declaration.id bindings).inputs name).1 ∈ values ∧
 ((capture state registry invocation declaration.id bindings).inputs name).2 ∈ values := by
 unfold capture
 dsimp only
 split
 · rename_i bounds same
   exact occurrences_endpoints supported name bounds (by rw [same]; exact List.mem_singleton_self _)
 · exact ⟨reserved (reservation state _ (input_key visible named (Or.inl rfl))),
     reserved (reservation state _ (input_key visible named (Or.inr rfl)))⟩

theorem report_capture
 (path : B4Target.Steps (Step registry initial root budget) initial.state state)
 (seed : state.seed = initial.state.seed)
 (parent : invocation ∈ GeneralNominalInvocationAncestry.frontier registry initial.state.seed root budget)
 (report : GeneralNominalRecursiveInspection.Report state)
 (visible : declaration ∈ registry.declarations) (named : name ∈ declaration.inputNames) :
 (capture state registry invocation declaration.id (GeneralNominalRecursiveInspection.bindings state report)).inputs name
   ∈ GeneralNominalRebaseAggregateFinite242.endpointPairs (pool registry initial root budget) :=
 GeneralNominalRebaseAggregateFinite242.endpointPairs_mem.mpr
   (capture_supported (GeneralNominalRebaseEndpointProducer243.report_endpoints path report)
     (GeneralNominalRebaseStablePool243.reserved_supported seed parent) visible named)

def functions (values : List α) : (n : Nat) → List (Fin n → α)
 | 0 => [fun index => Fin.elim0 index]
 | n+1 => values.flatMap fun head => (functions values n).map fun tail => Fin.cases head tail

theorem functions_mem (values : List α) (f : Fin n → α) (included : ∀ index, f index ∈ values) :
 f ∈ functions values n := by
 induction n with
 | zero =>
   have eq : f = fun index => Fin.elim0 index := by funext index; exact Fin.elim0 index
   exact eq ▸ List.mem_singleton_self _
 | succ n ih =>
   have tail := ih (fun index => f index.succ) (fun index => included index.succ)
   have same : Fin.cases (f 0) (fun index => f index.succ) = f := by
     funext index
     exact Fin.cases rfl (fun _ => rfl) index
   exact List.mem_flatMap.mpr ⟨f 0,included 0,List.mem_map.mpr ⟨_,tail,same⟩⟩

theorem functions_length (values : List α) (n : Nat) : (functions values n).length = values.length ^ n := by
 induction n with
 | zero => rfl
 | succ n ih =>
   have blocks (items : List α) : (items.flatMap fun head => (functions values n).map fun tail => (Fin.cases head tail : Fin (n+1) → α)).length =
       items.length * values.length ^ n := by
     induction items with
     | nil => simp
     | cons head rest previous => simp only [List.flatMap_cons,List.length_append,List.length_map,ih,previous,List.length_cons,Nat.add_mul,Nat.one_mul]; omega
   exact (blocks values).trans (by rw [Nat.pow_succ,Nat.mul_comm])
end Yulang.GeneralNominalRebaseCaptureProducer243
