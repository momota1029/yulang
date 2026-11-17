import Yulang.GeneralNominalRebaseChildProducer243
namespace Yulang.GeneralNominalRebaseChildrenUniverse243
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalAllocation
open GeneralNominalRebaseStablePool243 (pool)
open GeneralNominalRebaseChildProducer243

def childrenPool (registry : Registry) (checked : Checked registry)
 (initial : GeneralNominalCandidates.Context) (root budget : Nat) : List (Occurrence registry.roles) :=
 (GeneralNominalInvocationAncestry.frontier registry initial.state.seed root budget).flatMap fun invocation =>
 registry.declarations.attach.flatMap fun declaration =>
 declaration.val.requirements.attach.flatMap fun clause =>
 (candidates initial.state registry invocation declaration.val clause.val
   ((checked.2 declaration.val declaration.property).signature.2.2.2 clause.val clause.property)
   (pool registry initial root budget)).map fun demand =>
 ⟨source initial.state registry invocation (origin invocation declaration.val.id 6 clause.val.id 0), demand⟩

theorem emitted_member
 (checked : Checked registry)
 (path : B4Target.Steps (GeneralNominalRebaseSourceSteps243.Step registry initial root budget) initial.state state)
 (seed : state.seed = initial.state.seed)
 (parent : site.identity ∈ GeneralNominalInvocationAncestry.frontier registry initial.state.seed root budget)
 (report : GeneralNominalRecursiveInspection.Report state)
 (visible : declaration ∈ registry.declarations)
 (member : child ∈ children state registry site declaration (checked.2 declaration visible)
   (GeneralNominalRecursiveInspection.bindings state report)) :
 child ∈ childrenPool registry checked initial root budget := by
 unfold children GeneralDictionaryEmissionPlans.children at member
 obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
 have old := (GeneralCanonicalChildOrder.canonicalEmit_perm site.identity declaration
   (checked.2 declaration visible) _ _).mem_iff.mpr present
 unfold GeneralDeclarationDemands.emitAll at old
 obtain ⟨clause,_,same⟩ := List.mem_map.mp old
 cases same
 apply List.mem_flatMap.mpr
 refine ⟨site.identity,parent,List.mem_flatMap.mpr ?_⟩
 refine ⟨⟨declaration,visible⟩,List.mem_attach _ _,List.mem_flatMap.mpr ?_⟩
 refine ⟨clause,List.mem_attach _ _,List.mem_map.mpr ?_⟩
 refine ⟨_,trace_child path seed parent report visible (checked.2 declaration visible).scope
   clause.property ((checked.2 declaration visible).signature.2.2.2 clause.val clause.property),?_⟩
 dsimp only [GeneralDictionaryEmissionPlans.occurrence, GeneralDeclarationDemands.emit,
   frame, source]
 rw [seed]
end Yulang.GeneralNominalRebaseChildrenUniverse243
