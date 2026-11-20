import Yulang.GeneralObservedMetadataReport290

/-! The chosen scope includes all recorded descriptors and all normalized
heads in the explicit candidate list. An omitted declaration is not covered. -/
namespace Yulang.GeneralObservedMetadataScope290
open GeneralDeclarationPatterns (Constructors)
open GeneralDeclarations (Declaration)
open GeneralNominalInspection (Interpretation Bounds)
open GeneralNominalState (State Descriptor)
open GeneralObservedMetadataKeys290 (candidateKeys headKeys candidate_key)
open GeneralObservedMetadataEntry290 (LocalEqual agree agree_exact)
open GeneralObservedMetadataLocal290 (LocalPrimitiveOK primitiveOK primitiveOK_exact)
open GeneralRebaseReceiptCatalogue289 (constructorKeys)

def coverage (state : State) (ds : List Declaration) : List Nat :=
  constructorKeys state ++ candidateKeys ds

theorem descriptor_key (s : State) (slot : Fin s.base.slots) (d : Descriptor s.base.slots)
    (found : s.nominals slot = some d) : d.constructor ∈ constructorKeys s := by
  unfold constructorKeys
  apply List.mem_filterMap.mpr
  refine ⟨some d.constructor,List.mem_ofFn.mpr ⟨slot,?_⟩,rfl⟩
  rw [found,Option.map_some]

theorem covers_descriptor (s : State) (ds : List Declaration) (slot : Fin s.base.slots)
    (d : Descriptor s.base.slots) (found : s.nominals slot = some d) :
    d.constructor ∈ coverage s ds :=
  List.mem_append_left _ (descriptor_key s slot d found)

theorem covers_head (s : State) (ds : List Declaration) {d : Declaration} {k : Nat}
    (visible : d ∈ ds) (head : k ∈ headKeys d) : k ∈ coverage s ds :=
  List.mem_append_right _ (candidate_key visible head)

inductive Result where
  | good
  | disagreement
  | incompatiblePrimitive
  deriving DecidableEq, Repr

def certify (keys : List Nat) (first : Constructors) (i : Interpretation)
    (last : Constructors) (j : Interpretation) : Result :=
  if !agree keys first i last j then .disagreement
  else if primitiveOK keys last j then .good else .incompatiblePrimitive

theorem good_exact (keys : List Nat) (first : Constructors) (i : Interpretation)
    (last : Constructors) (j : Interpretation) :
    certify keys first i last j = .good ↔
      LocalEqual keys first i last j ∧ LocalPrimitiveOK keys last j := by
  cases a : agree keys first i last j <;> cases b : primitiveOK keys last j <;>
    simp [certify,a,b,← agree_exact,← primitiveOK_exact]

theorem disagreement_exact (keys : List Nat) (first : Constructors) (i : Interpretation)
    (last : Constructors) (j : Interpretation) :
    certify keys first i last j = .disagreement ↔ ¬ LocalEqual keys first i last j := by
  cases a : agree keys first i last j <;> cases b : primitiveOK keys last j <;>
    simp [certify,a,b,← agree_exact]

theorem incompatible_exact (keys : List Nat) (first : Constructors) (i : Interpretation)
    (last : Constructors) (j : Interpretation) :
    certify keys first i last j = .incompatiblePrimitive ↔
      LocalEqual keys first i last j ∧ ¬ LocalPrimitiveOK keys last j := by
  cases a : agree keys first i last j <;> cases b : primitiveOK keys last j <;>
    simp [certify,a,b,← agree_exact,← primitiveOK_exact]

theorem accepted_report (s : State) (ds : List Declaration) (first : Constructors)
    (i : Interpretation) (last : Constructors) (j : Interpretation)
    (good : certify (coverage s ds) first i last j = .good) (d : Declaration)
    (member : d ∈ ds) (bounds : List (Bounds s)) :
    GeneralObservedMetadataReport290.reportFrom s first i d bounds =
      GeneralObservedMetadataReport290.reportFrom s last j d bounds :=
  GeneralObservedMetadataReport290.report_eq _ _ _ _ _ _ _ (((good_exact ..).mp good).1.restrict
    (fun _ present => covers_head s ds member present))

theorem accepted_recorded (s : State) (ds : List Declaration) (i : Interpretation)
    (last : Constructors) (j : Interpretation)
    (good : certify (coverage s ds) s.constructors i last j = .good)
    (slot : Fin s.base.slots) (d : Descriptor s.base.slots) (found : s.nominals slot = some d) :
    last d.constructor = some d.declaration := by
  have overlap := ((good_exact ..).mp good).1 _ (covers_descriptor s ds slot d found)
  exact overlap.1.symm.trans (s.catalogue slot d found)

end Yulang.GeneralObservedMetadataScope290
