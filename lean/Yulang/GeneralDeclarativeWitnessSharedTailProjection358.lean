import Yulang.GeneralDeclarativeWitnessAuthoredProjection358

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSharedTailProjection358
open CommonNominalFullCarrier (Ty Equivalent record observeTy)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWitnessDeclaredState357 (centerEq)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source links)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans union_congr record_congr eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open PresenceNormalForm (Atom)

theorem record_merge_shared_tail (label : Nat) (a b rest : Ty) :
    Equivalent (.union (record label a rest) (record label b rest)) (record label (.union a b) rest) := by
  constructor <;> intro depth <;> cases depth with
  | zero =>
      simp only [observeTy,record,CommonNominalSyntax.Layer.evalAt,CommonNominalSyntax.observe]
      first
      | exact (CommonNominalFullDemand.producerEq_union_absorb (CommonNominalFullDemand.producerLe_refl _)).1
      | exact (CommonNominalFullDemand.producerEq_union_absorb (CommonNominalFullDemand.producerLe_refl _)).2
  | succ depth =>
      first
      | exact (CommonNominalFullDemand.record_union_payload label _ _ _).2
      | exact (CommonNominalFullDemand.record_union_payload label _ _ _).1

def field (root label head rest : Nat) : Equation :=
  ⟨root,.record label (.variable head) (.variable rest)⟩

structure Range where
  label : Nat
  aRoot : Nat
  bRoot : Nat
  aField : Nat
  bField : Nat
  remainder : Nat
  outer : Capture
  projected : Capture

def rows (r : Range) : List Equation :=
  [field r.aRoot r.label r.aField r.remainder,field r.bRoot r.label r.bField r.remainder,
   centerEq r.outer.center r.aRoot r.bRoot,
   centerEq r.projected.lower r.aField r.bField,
   centerEq r.projected.center r.aField r.bField,
   centerEq r.projected.upper r.aField r.bField]

structure Supported (source : Source) (s : State) (r : Range) : Prop where
  original : ∀ line ∈ rows r,line ∈ source.authored
  current : ∀ line ∈ rows r,line ∈ s.equations
  retainedBounds : ∀ atom ∈ links r.outer,atom ∈ s.normal.ordinary

def check (source : Source) (s : State) (r : Range) : Bool :=
  (rows r).all (fun row => decide (row ∈ source.authored)) &&
  (rows r).all (fun row => decide (row ∈ s.equations)) &&
  (links r.outer).all (fun atom => decide (atom ∈ s.normal.ordinary))

theorem check_exact {src s r} : check src s r = true ↔ Supported src s r := by
  simp only [check,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1,h.1.2,h.2⟩,fun e => ⟨⟨e.original,e.current⟩,e.retainedBounds⟩⟩

theorem authored_visibility_same_model {src s r} (built : Supported src s r)
    (m : Assignment) (valid : Models s m) :
    Equivalent (m r.outer.lower).1 (record r.label (m r.projected.lower).1 (m r.remainder).1) ∧
    Equivalent (m r.outer.center).1 (record r.label (m r.projected.center).1 (m r.remainder).1) ∧
    Equivalent (m r.outer.upper).1 (record r.label (m r.projected.upper).1 (m r.remainder).1) := by
  have left : Equivalent (m r.aRoot).1 (record r.label (m r.aField).1 (m r.remainder).1) :=
    valid.2 (field r.aRoot r.label r.aField r.remainder) (built.current _ (by simp [rows]))
  have right : Equivalent (m r.bRoot).1 (record r.label (m r.bField).1 (m r.remainder).1) :=
    valid.2 (field r.bRoot r.label r.bField r.remainder) (built.current _ (by simp [rows]))
  have center : Equivalent (m r.outer.center).1 (.union (m r.aRoot).1 (m r.bRoot).1) :=
    valid.2 (centerEq r.outer.center r.aRoot r.bRoot) (built.current _ (by simp [rows]))
  have joined := eqv_trans center (eqv_trans (union_congr left right)
    (record_merge_shared_tail r.label (m r.aField).1 (m r.bField).1 (m r.remainder).1))
  have lo : Equivalent (m r.outer.lower).1 (m r.outer.center).1 :=
    ⟨valid.1.1 _ (built.retainedBounds (.tyLe (.var r.outer.lower) (.var r.outer.center)) (by simp [links])),
     valid.1.1 _ (built.retainedBounds (.tyLe (.var r.outer.center) (.var r.outer.lower)) (by simp [links]))⟩
  have hi : Equivalent (m r.outer.upper).1 (m r.outer.center).1 :=
    ⟨valid.1.1 _ (built.retainedBounds (.tyLe (.var r.outer.upper) (.var r.outer.center)) (by simp [links])),
     valid.1.1 _ (built.retainedBounds (.tyLe (.var r.outer.center) (.var r.outer.upper)) (by simp [links]))⟩
  have atPayload {slot} (observed : centerEq slot r.aField r.bField ∈ rows r) :
      Equivalent (m slot).1 (.union (m r.aField).1 (m r.bField).1) :=
    valid.2 _ (built.current _ observed)
  have seen {slot} (observed : centerEq slot r.aField r.bField ∈ rows r) :=
    eqv_trans joined (record_congr r.label ⟨(atPayload observed).2,(atPayload observed).1⟩
      (eqv_refl (m r.remainder).1))
  exact ⟨eqv_trans lo (seen (by simp [rows])),seen (by simp [rows]),
    eqv_trans hi (seen (by simp [rows]))⟩

end Yulang.GeneralDeclarativeWitnessSharedTailProjection358
