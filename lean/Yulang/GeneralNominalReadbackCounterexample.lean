import Yulang.GeneralNominalSourceFormation

/-! A finite, source-formed nonpoint nominal input separates interval capture
from endpoint-exact finite-pattern readback. The existing general Survivor and
cycle-based Local are used throughout. No alternate classifier is introduced. -/
namespace Yulang.GeneralNominalReadbackCounterexample

open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open CommonNominalFullCarrier
open GeneralDeclarationExamples (roles constructors display display_checked)

abbrev source := GeneralNominalIntervalExamples.source
abbrev context := GeneralNominalRecursiveExamples.nonpointContext
abbrev root := GeneralNominalRecursiveExamples.nonpointRoot
abbrev registry : Registry := ⟨constructors,roles,[display]⟩
abbrev children := GeneralNominalRecursiveExamples.nonpointChildren
abbrev model := GeneralNominalIntervalExamples.model .int .int

abbrev child : Occurrence roles :=
  ⟨GeneralNominalAllocation.source source registry root.identity
    (GeneralNominalAllocation.origin root.identity display.id 6 10 0),
    ⟨0,fun _ => (2,3),[],by intro _ member; cases member⟩⟩

theorem checked : Checked registry :=
  ⟨by decide +kernel,by intro declaration member; have same := List.mem_singleton.mp member; subst declaration; exact display_checked⟩

theorem children_exact : children = [child] := by
  unfold children GeneralNominalRecursiveExamples.nonpointChildren GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  simp [GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralNominalAllocation.frame,
    GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,normalize,child]
  rfl

theorem prepared : GeneralNominalRecursiveCandidates.Prepared registry context root display display_checked := by
  have original := GeneralNominalRecursiveExamples.nonpoint_survivor .int .int
  obtain ⟨_,declaration,visible,certified,identity,role,bounds,located,ready,_⟩ := original
  have same : declaration = display := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · cases identity
    · rfl
    · cases identity
  subst declaration
  obtain ⟨metadata,linked,_,bounds,located,finished,requestReady,consistent⟩ := ready
  exact ⟨metadata,linked,GeneralNominalUnaryCaptureFacts.initial_fresh source registry root.identity (by decide +kernel),
    bounds,located,finished,requestReady,consistent⟩

theorem survivor : GeneralNominalRecursiveCandidates.Survivor registry context root 1 children := by
  refine ⟨(GeneralNominalRecursiveExamples.nonpoint_survivor .int .int).1,display,by simp,display_checked,
    rfl,rfl,[(0,0)],by decide +kernel,prepared,?_⟩
  have query : GeneralNominalInspection.queries source context.interpretation display = [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]
  rw [GeneralNominalUnaryCaptureFacts.report_exact context display 0 GeneralNominalIntervalExamples.descriptor
    rfl 0 (2,3) rfl query]
  rfl

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry context root := by
  have ready := prepared
  obtain ⟨metadata,linked,_⟩ := ready
  refine ⟨rfl,metadata,linked,(by intro model _ index; exact subtype_refl _),?_,rfl⟩
  intro identity member
  have bound := GeneralNominalAllocation.member_le_max (GeneralNominalState.sources source) identity member
  exact Nat.le_trans bound (by decide +kernel)

theorem formed : GeneralNominalSourceFormation.SourceFormed registry root
    (GeneralNominalSaturationState.initial context root) := .initial context initial_source

private theorem int_not_nominal : ¬ Subtype (.base .int) (nominal 0 [.inl (.base .int)]) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead 0 1) (by exact ⟨rfl,rfl⟩)

private theorem int_not_bottom : ¬ Subtype (.base .int) .bottom := by
  intro below
  have impossible := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.base .str) (by trivial)
  cases impossible

private theorem small_value (slot : Fin source.base.slots) (small : slot.val < 2) :
    (model (source.base.source slot)).1 = nominal 0 [.inl (.base .int)] := by
  have cases : slot.val = 0 ∨ slot.val = 1 := by omega
  rcases cases with h | h <;> simp [h] <;> rfl

private theorem edge_bounds (first last : Fin source.base.slots)
    (edge : GeneralNominalCycleK2.Edge source first last) : first.val < 2 ∧ ¬ last.val < 2 := by
  rcases edge with structural | ⟨descriptor,recorded,index,observations⟩
  · obtain ⟨kind,_,_,_,_⟩ := structural
    exact Fin.elim0 kind
  · have small : first.val < 2 := by
      by_cases yes : first.val < 2
      · exact yes
      · simp [source,GeneralNominalIntervalExamples.source,yes] at recorded
    have same : descriptor = GeneralNominalIntervalExamples.descriptor := by
      simpa [source,GeneralNominalIntervalExamples.source,small] using recorded.symm
    subst descriptor
    refine ⟨small,?_⟩
    intro targetSmall
    obtain ⟨actual,seen,equal⟩ := observations model (GeneralNominalIntervalExamples.source_models .int .int)
    cases seen with
    | argument observed same found =>
      cases observed
      rw [small_value first small] at same
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp same.1
      have size := invariant.2.1
      have indexZero : index = 0 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        simp only [List.length_cons,List.length_nil] at size
        omega
      subst index
      have argument := invariant.2.2 0 (.inl (.base .int)) (.inl actual) rfl found
      rw [small_value last targetSmall] at equal
      exact int_not_nominal (subtype_trans argument.1 equal.1)

theorem no_cycle (slot : Fin source.base.slots) : ¬ GeneralNominalCycleK2.Cycle source slot := by
  rintro ⟨child,edge,path⟩
  have bounds := edge_bounds slot child edge
  cases path with
  | nil => exact bounds.2 bounds.1
  | cons next _ => exact bounds.2 (edge_bounds _ _ next).1

private theorem legacy_clear (slot : Fin source.base.slots) :
    ¬ GeneralNominalMixedRecurrence.RecursAt source slot := by
  rintro ⟨⟨kind,_,_⟩,_⟩
  exact Fin.elim0 kind

theorem selected : GeneralNominalCycleK2.Local registry context root (.selected 1 children) := by
  refine .selected ⟨survivor.1,?_,?_,?_⟩ ⟨survivor,?_⟩
  · rintro ⟨_,_,_,slot,_,cycle⟩
    exact no_cycle slot (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · rintro ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩
    exact no_cycle visited.1 (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,declaration,visible,_,_,_,missing⟩ := pending
      have same := List.mem_singleton.mp visible; subst declaration
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · exact legacy_clear slot cycle
      · exact legacy_clear visited.1 cycle
  · intro key emitted found
    have copy := found
    obtain ⟨_,declaration,visible,_,identity,_⟩ := found
    have same := List.mem_singleton.mp visible; subst declaration
    have same : key = 1 := identity.symm; subst key
    exact ⟨rfl,GeneralNominalRecursiveCandidates.survivor_children_functional registry checked context root 1 _ _ copy survivor⟩

/-- The stronger endpoint-exact interpretation of the old pattern labels.
Only the lower half is needed to exhibit the obstruction. -/
def LowerExact (readback : GeneralNominalCycleReadback.Readback roles registry context)
    (interpret : Pattern → Ty) : Prop :=
  ∀ demand : Occurrence roles, ∀ index : Fin (roles demand.demand.role).arity,
    ∀ pattern, (readback.lower demand)[index.val]? = some pattern →
      Equivalent (interpret pattern) (model (demand.demand.arguments index).1).1

theorem endpoint_exact_readback_impossible
    (readback : GeneralNominalCycleReadback.Readback roles registry context) (interpret : Pattern → Ty)
    (nominal : ∀ pattern, Equivalent (interpret (.app 0 [pattern])) (CommonNominalFullCarrier.nominal 0 [.inl (interpret pattern)])) :
    ¬ LowerExact readback interpret := by
  intro exactLower
  have member : child ∈ children := by rw [children_exact]; simp
  obtain ⟨declaration,visible,_,_,_,_,_,_,clause,present,_,lo,hi,parent,_,nested,_⟩ :=
    readback.selected root 1 children selected child member
  have same := List.mem_singleton.mp visible; subst declaration
  have same := List.mem_singleton.mp present; subst clause
  have parentValue := exactLower root ⟨0,by decide +kernel⟩ (.app 0 [lo 0]) (by rw [parent]; rfl)
  have childValue := exactLower child ⟨0,by decide +kernel⟩ (lo 0) (by rw [nested]; rfl)
  change Equivalent (interpret (.app 0 [lo 0])) (CommonNominalFullCarrier.nominal 0 [.inl (.base .int)]) at parentValue
  change Equivalent (interpret (lo 0)) .bottom at childValue
  have below := subtype_trans parentValue.2 (nominal (lo 0)).1
  have argument := ((nominal_regular_invariant_exact _ _ _ _).mp below).2.2 0
    (.inl (.base .int)) (.inl (interpret (lo 0))) rfl rfl
  exact int_not_bottom (subtype_trans argument.1 childValue.1)

end Yulang.GeneralNominalReadbackCounterexample
