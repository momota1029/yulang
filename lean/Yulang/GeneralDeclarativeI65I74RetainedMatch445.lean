import Yulang.GeneralDeclarativeI65I74RetainSelected445

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open MixedFixed442
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open CommonDeclaredNominalInspection (Parameter)
open CommonRecursiveNominalIntervals (effectiveParameter)
open CommonNominalFullCarrier (Equivalent nominal)

/-- These are finite syntactic observations, not model values.
Both originals and the stored data expose the ordered original binders,
kinds, variances and full interval names. -/
structure RefCoordinates where
  key : Nat
  rowBinder : Nat
  valueBinder : Nat
  rowLower : Nat
  rowCenter : Nat
  rowUpper : Nat
  valueLower : Nat
  valueCenter : Nat
  valueUpper : Nat
  parameters : List Nat
  deriving DecidableEq

def coordinates (key r v : Nat) (rc vc : Capture) (a b : Parameter) : RefCoordinates :=
  ⟨key,r,v,rc.lower,rc.center,rc.upper,vc.lower,vc.center,vc.upper,
    Check408.paramCode a ++ Check408.paramCode b⟩

/-- Shape of the exact named, mixed RHS. The evidence is a syntax
constructor, with no model equality or submitted assertion. -/
inductive RefShape {s : GeneralDeclarativeI65.State} {slots : Nat → Option Capture} :
    {c : Bool} → {p : GeneralDeclarationPatterns.Pattern} →
      NamedMixedTree401 s slots c p → Type where
  | intro {c : Bool} {a b : Parameter} {key r v : Nat}
      (use : Use s.current.environment key 2)
      (mode : names use.mode 2 = some [a,b]) (table : s.modes[key]? = some [a,b])
      (rk : a.kind = .row) (rm : (effectiveParameter c a).variance ≠ .invariant)
      (vk : b.kind = .value) (vm : (effectiveParameter c b).variance = .invariant)
      (rc : NamedSlot401 slots .row r) (vc : NamedSlot401 slots .value v) :
      RefShape (.declaredApp key use mode table
        (.cons (.rowPoint r rk rm rc) (.cons (.valueInterval v vk vm vc) .nil)))

def RefShape.coordinates {s slots c p} {t : NamedMixedTree401 s slots c p} :
    RefShape t → RefCoordinates
  | @RefShape.intro _ _ _ a b key r v _ _ _ _ _ _ _ rc vc =>
    RetainedFull445.coordinates key r v rc.val vc.val a b

def readRefShape {s slots c p} (t : NamedMixedTree401 s slots c p) : Option (RefShape t) :=
  match t with
  | @MixedRhs401.declaredApp _ _ [_,_] _ _ _ use mode table
      (.cons (.rowPoint _ rk rm rc) (.cons (.valueInterval _ vk vm vc) .nil)) =>
    some (.intro use mode table rk rm vk vm rc vc)
  | _ => none

theorem exact_shape_is_read445 {s slots c p} {t : NamedMixedTree401 s slots c p} (h : RefShape t) :
    readRefShape t = some h := by
  cases h
  rfl

theorem shaped_rhs_exact_value445 {s slots c p} {t : NamedMixedTree401 s slots c p}
    (h : RefShape t) (m : I72.Model) :
    evaluateMixedRhs401 (actualNamedMixedRead401 m) t =
      some (nominal h.coordinates.key
        [.inr (m.assignment h.coordinates.rowCenter).2,
         .inl (m.assignment h.coordinates.valueCenter).1]) := by
  cases h
  rfl

structure RowKey where
  occurrence : List Nat
  declarationOrdinal : Nat
  outputOrdinal : Nat
  output : GeneralSourceState.Output
  body : GeneralDictionaryAssociatedProvenance.Body
  rhs : RefCoordinates
  deriving DecidableEq

def storedKey {s : I72.State} (r : RetainedEquation s) (h : RefShape r.rhs) : RowKey :=
  ⟨r.occurrence,r.declarationOrdinal,r.outputOrdinal.val,
    r.request.demand.outputs[r.outputOrdinal],r.body,h.coordinates⟩

def eventKey {p : Problem} (source : SourceSelection p) : RowKey :=
  let r := source.origin
  let a := source.own.2.out
  ⟨p.root.occurrence,r.event.frame.ordinal,r.i0.val,p.root.demand.outputs[r.i0],
    a.named.body,coordinates a.key a.rowBinder a.valueBinder a.rowCap a.valueCap
      RefPositions441.rowCov RefPositions441.valueInv⟩

/-- Source-facing relation; both the row and the original selection are
indexed by precisely this snapshot. No Boolean result is a premise. -/
structure StoredSelection (s : FullState) {q : I72.Request}
    (source : SourceSelection ⟨s.base,q⟩) : Type where
  row : RetainedEquation s.base
  member : row ∈ s.retained
  shape : RefShape row.rhs
  exactKey : storedKey row shape = eventKey source

theorem stored_selection_means_iff_exact_targets445 {s : FullState} {q : I72.Request}
    {source : SourceSelection ⟨s.base,q⟩} (kept : StoredSelection s source) (m : I72.Model) :
    kept.row.Means m ↔ FixedTargets m source.origin.event := by
  let r := source.origin
  let a := source.own.2.out
  rw [original_replayed_ref_is_the_fixed_target_slice442 r a m]
  have actual : kept.row.output.receipt.actualEquation m =
      some (kept.row.target,nominal kept.shape.coordinates.key
        [.inr (m.assignment kept.shape.coordinates.rowCenter).2,
         .inl (m.assignment kept.shape.coordinates.valueCenter).1]) := by
    unfold NamedMixedReceipt401.actualEquation
    change (evaluateMixedRhs401 (actualNamedMixedRead401 m) kept.row.rhs).map _ = _
    rw [shaped_rhs_exact_value445 kept.shape m]
    rfl
  have centerRow := congrArg (fun key : RowKey => key.rhs.rowCenter) kept.exactKey
  have centerVal := congrArg (fun key : RowKey => key.rhs.valueCenter) kept.exactKey
  have key := congrArg (fun key : RowKey => key.rhs.key) kept.exactKey
  have target := congrArg (fun key : RowKey => key.output.target) kept.exactKey
  change kept.shape.coordinates.rowCenter = a.rowCap.center at centerRow
  change kept.shape.coordinates.valueCenter = a.valueCap.center at centerVal
  change kept.shape.coordinates.key = a.key at key
  change kept.row.target = q.demand.outputs[r.i0].target at target
  unfold RetainedEquation.Means
  rw [actual,centerRow,centerVal,key,target]
  change (∃ ty, some (q.demand.outputs[r.i0].target,a.actualValue m) =
    some (q.demand.outputs[r.i0].target,ty) ∧
    Equivalent (m.assignment q.demand.outputs[r.i0].target).1 ty) ↔
    Equivalent (m.assignment q.demand.outputs[r.i0].target).1 (a.actualValue m)
  exact ⟨fun ⟨v,h,eq⟩ => (Prod.mk.inj (Option.some.inj h)).2.symm ▸ eq,fun eq => ⟨_,rfl,eq⟩⟩

theorem stored_selection_fixed_targets445 {s : FullState} {q : I72.Request}
    {source : SourceSelection ⟨s.base,q⟩} (kept : StoredSelection s source)
    (m : I72.Model) (fit : FitsFull s m) :
    FixedTargets m source.origin.event :=
  (stored_selection_means_iff_exact_targets445 kept m).mp (fit.2 kept.row kept.member)

def rowMatches {s : I72.State} (r : RetainedEquation s) (key : RowKey) : Bool :=
  match readRefShape r.rhs with
  | none => false
  | some shape => decide (storedKey r shape = key)

theorem read_stored_selection445 {s : FullState} {q : I72.Request}
    {source : SourceSelection ⟨s.base,q⟩}
    (h : s.retained.any (fun row => rowMatches row (eventKey source)) = true) :
    Nonempty (StoredSelection s source) := by
  obtain ⟨r,member,matched⟩ := List.any_eq_true.mp h
  unfold rowMatches at matched
  cases got : readRefShape r.rhs with
  | none => simp [got] at matched
  | some shape =>
    have eq : storedKey r shape = eventKey source := by simpa only [got,decide_eq_true_eq] using matched
    exact ⟨⟨r,member,shape,eq⟩⟩

theorem stored_selection_matches445 {s : FullState} {q : I72.Request}
    {source : SourceSelection ⟨s.base,q⟩} (a : StoredSelection s source) :
    s.retained.any (fun row => rowMatches row (eventKey source)) = true :=
  List.any_eq_true.mpr ⟨a.row,a.member,by simp [rowMatches,exact_shape_is_read445 a.shape,a.exactKey]⟩

end Yulang.GeneralDeclarativeI65.I72.RetainedFull445
