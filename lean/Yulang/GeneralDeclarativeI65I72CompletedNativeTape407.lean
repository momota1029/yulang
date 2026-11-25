import Yulang.GeneralDeclarativeI65I72CompletedNativeRival406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)

abbrev visibleKey407 (q : Request) (d : Declaration) : Bool := d.role == q.demand.role

structure VisibleUnary407 (s : State) (row : Declaration) where
  key : Nat
  binder : Nat
  literal : row.head = [authoredUnaryPattern405 key binder]
  use : Use s.core.current.environment key 1
  declared : ∃ ps, use.mode = .declared ps

abbrev VisibleIndex407 (s : State) (q : Request) := Fin (visible s.core q).length

structure VisibleRoot407 (s : State) (q : Request) (idx : VisibleIndex407 s q) where
  unary : VisibleUnary407 s (visible s.core q)[idx]
  sourceOrdinal : Nat
  sourceIndex : unfilterOrdinal395 (visibleKey407 q)
    (authoredRegistry s.core.current).declarations idx = some sourceOrdinal
  declarationAt : (authoredRegistry s.core.current).declarations[sourceOrdinal]? = some (visible s.core q)[idx]

theorem exact_visible_root407 {s q} (unary : ∀ i : VisibleIndex407 s q, VisibleUnary407 s (visible s.core q)[i])
    (idx : VisibleIndex407 s q) : Nonempty (VisibleRoot407 s q idx) := by
  have atIndex : (visible s.core q)[idx.val]? = some (visible s.core q)[idx] :=
    List.getElem?_eq_getElem idx.isLt
  obtain ⟨sourceOrdinal, sourceIndex, declarationAt⟩ :=
    unfilterOrdinal395_exact (visibleKey407 q) (authoredRegistry s.core.current).declarations idx.val atIndex
  exact ⟨⟨unary idx,sourceOrdinal,sourceIndex,declarationAt⟩⟩

def VisibleRoot407.visit {s q idx} (atRoot : VisibleRoot407 s q idx) (arg : Capture) : CandidateVisit :=
  ⟨atRoot.sourceOrdinal,0,[],.value,false,arg.lower⟩

theorem exact_visible_roots_are_ordered407 {s q}
    (roots : ∀ i : VisibleIndex407 s q, VisibleRoot407 s q i) {i j : VisibleIndex407 s q}
    (h : i.val < j.val) : (roots i).sourceOrdinal < (roots j).sourceOrdinal :=
  unfilter_keeps_original_order405 (visibleKey407 q) (authoredRegistry s.core.current).declarations
    h (roots i).sourceIndex (roots j).sourceIndex

theorem exact_visible_roots_are_unique407 {s q idx} (a b : VisibleRoot407 s q idx) :
    a.sourceOrdinal = b.sourceOrdinal := Option.some.inj (a.sourceIndex.symm.trans b.sourceIndex)

structure CompletedRead407 (s : State) (q : Request) (need : OutputNeed s) where
  arg : Capture
  argAt : q.demand.arguments = [arg]
  found : Nat
  sourcePayload : Nat
  fixesLower : need.expected.original.target = arg.lower
  sourceType : TypedCovariantPoint404 found sourcePayload need.expected.rhs

theorem completed_read_is_literal_and_retained407 {s q p d original}
    (selectedProducer : FiniteNative406 s p d original) (i : Fin p.demand.outputs.length)
    (read : CompletedRead407 s q ⟨p,d,i,original i⟩) :
    (⟨read.arg.lower,.nominal read.found [.variable read.sourcePayload]⟩ : Equation)
      ∈ s.core.current.ordinary.equations ∧ DeclaredHead404 read.found (original i).rhs := by
  have source := actual_typed_point_yields_literal_declared_code404 (original i).rhs read.sourceType
  exact ⟨chosen_finite_native_output_retains_exact_nominal406 selectedProducer i read.fixesLower source.1 source.2,
    source.1⟩

/-- A scan annotates a literal visit with outer-tag agreement or positive
evidence of a mismatch. Agreement is not a whole-candidate success. -/
def TagAgrees407 {s q need idx} (read : CompletedRead407 s q need) (root : VisibleRoot407 s q idx) : Bool :=
  root.unary.key == read.found

def CompletedVisits407 {s q need}
    (read : CompletedRead407 s q need) (roots : ∀ i : VisibleIndex407 s q, VisibleRoot407 s q i) :
    List CandidateVisit := List.ofFn fun i => (roots i).visit read.arg

theorem completed_visits_at_exact_visible_ordinals407 {s q need}
    (read : CompletedRead407 s q need) (roots : ∀ i : VisibleIndex407 s q, VisibleRoot407 s q i) :
    (CompletedVisits407 read roots).length = (visible s.core q).length ∧
    ∀ j : VisibleIndex407 s q, (CompletedVisits407 read roots)[j.val]? = some ((roots j).visit read.arg) := by
  simp [CompletedVisits407]

theorem exact_source_classifies_tag407 {s q need idx} (read : CompletedRead407 s q need)
    (root : VisibleRoot407 s q idx) :
    (TagAgrees407 read root = true ↔ DeclaredHead404 root.unary.key need.expected.rhs) ∧
    (TagAgrees407 read root = false ↔ ¬ DeclaredHead404 root.unary.key need.expected.rhs) := by
  have known := (actual_typed_point_yields_literal_declared_code404 need.expected.rhs read.sourceType).1
  have iffTag : root.unary.key = read.found ↔ DeclaredHead404 root.unary.key need.expected.rhs :=
    ⟨fun eq => eq ▸ known, fun same => a_literal_typed_nominal_cannot_name_different_constructors406 _ same known⟩
  constructor
  · simpa [TagAgrees407] using iffTag
  · simpa [TagAgrees407] using not_congr iffTag

theorem ordered_completed_visits_use_only_raw_root407 {s q need}
    (read : CompletedRead407 s q need) (roots : ∀ i : VisibleIndex407 s q, VisibleRoot407 s q i)
    (safe : ¬ RootCycle s q) :
    ∀ visit ∈ CompletedVisits407 read roots, ¬CurrentCycleAt s visit.site := by
  intro visit entered cycle
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp entered
  rw [← hj] at cycle
  exact safe ⟨read.arg,by simp [read.argAt],cycle⟩

end Yulang.GeneralDeclarativeI65.I72
