import Yulang.GeneralDictionaryVersionedPacket231
import Yulang.GeneralNominalVersionedCandidates231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedPrepared231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Snapshot
open GeneralDictionaryUpper230Current
open GeneralDictionaryVersionedNames231

theorem raw_support : GeneralNominalState.sources extendedSnapshot ⊆ GeneralDictionaryVersionedSupport231.pool := by
  intro name member
  have smaller := GeneralDictionaryUpper230Support.support member
  exact List.mem_append_left [GeneralDictionaryOptionalInstall229.actual] smaller

theorem fresh : GeneralNominalVersionedAllocation231.Fresh extendedSnapshot registry root.identity newBindings := by
  intro k member collision
  change k ∈ [GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 newBindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 newBindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 newBindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 newBindings] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    exfalso
    first
    | exact fresh_outside 0 (raw_support collision)
    | exact fresh_outside 1 (raw_support collision)

theorem prepared : GeneralNominalVersionedCandidates231.Prepared registry extendedContext root declaration := by
  refine ⟨GeneralDictionaryOptionalInitial229.source.metadata,⟨?_,by intro output member; cases member⟩,
    [(0,0)],rfl,?_,?_,extended,GeneralDictionaryVersionedProjection231.head_models⟩
  · intro index
    constructor <;> exact GeneralNominalAllocationSupport.slot_source extendedSnapshot (0 : Fin 6)
  · change GeneralNominalVersionedAllocation231.Fresh extendedSnapshot registry root.identity packet.bindings
    rw [bindings_exact]
    exact fresh
  · rw [report_exact]
    exact ⟨rfl,rfl,rfl⟩

theorem children_empty :
    GeneralNominalVersionedCandidates231.children registry extendedContext root declaration declaration_checked [(0,0)] = [] := by
  unfold GeneralNominalVersionedCandidates231.children GeneralNominalVersionedFrame231.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem survivor : GeneralNominalVersionedCandidates231.Survivor registry extendedContext root declaration.id [] :=
  ⟨GeneralDictionaryUpper230Safety.known,declaration,List.mem_singleton_self _,declaration_checked,
    rfl,rfl,[(0,0)],rfl,prepared,children_empty.symm⟩

theorem unique : GeneralNominalVersionedCandidates231.Unique registry extendedContext root declaration.id [] := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

end Yulang.GeneralDictionaryVersionedPrepared231
