import Yulang.GeneralNominalRebaseCaptureProducer243
namespace Yulang.GeneralNominalRebaseChildProducer243
open GeneralDeclarations GeneralSourceDictionaries GeneralDeclarationPatterns
open GeneralNominalAllocationSupport GeneralNominalAllocation
open GeneralNominalRebaseCaptureProducer243
open GeneralDeclarationDemands (childDemand)

theorem normalized_variables (arguments : List Pattern) (pattern : Pattern)
 (present : pattern ∈ arguments) (member : name ∈ (normalize pattern).variables) :
 name ∈ variablesArgs (normalizeArgs arguments) := by
 induction arguments with
 | nil => cases present
 | cons head tail ih =>
   rcases List.mem_cons.mp present with rfl | later
   · exact List.mem_append_left _ member
   · exact List.mem_append_right _ (ih later)

theorem argument_key (visible : declaration ∈ registry.declarations)
 (required : clause ∈ declaration.requirements) (position : index < clause.arguments.length)
 (purpose : kind = 3 ∨ kind = 4) :
 origin root declaration.id kind clause.id index ∈ keys registry root := by
 rcases purpose with rfl | rfl <;>
 simp only [keys, declarationKeys, List.mem_flatMap, List.mem_append, List.mem_map,
   List.mem_cons, List.mem_range]
 · exact ⟨declaration,visible,Or.inr ⟨clause,required,Or.inl (Or.inr ⟨index,position,Or.inl rfl⟩)⟩⟩
 · exact ⟨declaration,visible,Or.inr ⟨clause,required,Or.inl (Or.inr ⟨index,position,Or.inr (Or.inl rfl)⟩)⟩⟩

theorem child_arguments
 (supported : Endpoints bindings values)
 (reservations : reserved state registry root ⊆ values)
 (visible : declaration ∈ registry.declarations) (scope : declaration.Scoped)
 (required : clause ∈ declaration.requirements) (valid : clause.Signature roles)
 (index : Fin (roles clause.role).arity) :
 let demand := childDemand declaration clause valid (capture state registry root declaration.id bindings)
   (allocation state registry root declaration.id clause)
 (demand.arguments index).1 ∈ values ∧ (demand.arguments index).2 ∈ values := by
 dsimp only [childDemand]
 unfold GeneralDeclarationDemands.inputInterval
 split
 · rename_i name same
   have named : name ∈ declaration.inputNames := scope.1 clause required name
     (normalized_variables clause.arguments _ (List.getElem_mem _) (by rw [same]; exact List.mem_singleton_self _))
   exact capture_supported supported reservations visible named
 · have bound : index.val < clause.arguments.length := by rw [valid.1]; exact index.isLt
   exact ⟨reservations (reservation state _ (argument_key visible required bound (Or.inl rfl))),
     reservations (reservation state _ (argument_key visible required bound (Or.inr rfl)))⟩

def candidates (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (clause : Clause) (valid : clause.Signature roles) (values : List Nat) :
 List (GeneralSourceState.Demand roles) :=
 (functions (GeneralNominalRebaseAggregateFinite242.endpointPairs values) (roles clause.role).arity).map
   fun inputs => { childDemand declaration clause valid (capture state registry root declaration.id [])
     (allocation state registry root declaration.id clause) with arguments := inputs }

theorem child_finite
 (supported : Endpoints bindings values)
 (reservations : reserved state registry root ⊆ values)
 (visible : declaration ∈ registry.declarations) (scope : declaration.Scoped)
 (required : clause ∈ declaration.requirements) (valid : clause.Signature roles) :
 childDemand declaration clause valid (capture state registry root declaration.id bindings)
   (allocation state registry root declaration.id clause)
 ∈ candidates state registry root declaration clause valid values := by
 apply List.mem_map.mpr
 refine ⟨_,functions_mem _ _ (fun index => GeneralNominalRebaseAggregateFinite242.endpointPairs_mem.mpr
   (child_arguments supported reservations visible scope required valid index)),?_⟩
 rfl

theorem candidates_length (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
 (declaration : Declaration) (clause : Clause) (valid : clause.Signature roles) (values : List Nat) :
 (candidates state registry root declaration clause valid values).length =
 (values.length * values.length) ^ (roles clause.role).arity := by
 unfold candidates
 dsimp only [childDemand]
 rw [List.length_map, functions_length]
 rw [GeneralNominalRebaseAggregateFinite242.endpointPairs_length]
theorem candidates_seed {roles : Roles.RoleDecls} {valid : clause.Signature roles} (same : state.seed = initial.seed) :
 candidates state registry root declaration clause valid values =
 candidates initial registry root declaration clause valid values := by
 have cap : capture state registry root declaration.id [] = capture initial registry root declaration.id [] := by
   unfold capture source
   rw [same]
 have alloc : allocation (roles := roles) state registry root declaration.id clause =
     allocation initial registry root declaration.id clause := by
   unfold allocation source
   rw [same]
 unfold candidates
 rw [cap,alloc]

theorem trace_child
 (path : B4Target.Steps (GeneralNominalRebaseSourceSteps243.Step registry initial root budget) initial.state state)
 (seed : state.seed = initial.state.seed)
 (parent : invocation ∈ GeneralNominalInvocationAncestry.frontier registry initial.state.seed root budget)
 (report : GeneralNominalRecursiveInspection.Report state)
 (visible : declaration ∈ registry.declarations) (scope : declaration.Scoped)
 (required : clause ∈ declaration.requirements) (valid : clause.Signature roles) :
 childDemand declaration clause valid
   (capture state registry invocation declaration.id (GeneralNominalRecursiveInspection.bindings state report))
   (allocation state registry invocation declaration.id clause)
 ∈ candidates initial.state registry invocation declaration clause valid
   (GeneralNominalRebaseStablePool243.pool registry initial root budget) := by
 rw [← candidates_seed seed]
 exact child_finite (GeneralNominalRebaseEndpointProducer243.report_endpoints path report)
   (GeneralNominalRebaseStablePool243.reserved_supported seed parent) visible scope required valid
end Yulang.GeneralNominalRebaseChildProducer243
