import Yulang.GeneralVersionedTightOperands315

set_option backward.isDefEq.respectTransparency false
/-! Exact cross-version comparison of the one-sided raw extrema. Unlike
observation version equality, cuts ignore order, duplicate occurrences and
redundant terms. They compare the complete join/meet, not paired intervals. -/
namespace Yulang.GeneralVersionedEndpointCuts315
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedFrame231 (capture frame)
open GeneralNominalAllocation (occurrences lower upper equations)
open GeneralNominalVersionedPlans231 (HeadModels variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCaptureMerges (lower_exact upper_exact equations_exact)
open GeneralNominalMaterialization (Mode)
open CommonNominalFullCarrier (Subtype Equivalent Ty subtype_refl subtype_trans)
open PresenceNormalForm (All)

abbrev occurs (p : Packet roles) (name : Nat) := occurrences p.bindings name
abbrev merged (p : Packet roles) (m : Assignment) :=
  All CommonNominalFullCarrier.model m
    (GeneralNominalVersionedAllocation231.merges p.context.state p.registry
      p.site.occurrence.identity p.declaration p.bindings)

theorem equations_of_many (p : Packet roles) (m : Assignment) (name : Nat)
    (named : name ∈ p.declaration.inputNames) (held : merged p m)
    (seen : occurs p name = a :: b :: cs) :
    Equivalent (m ((capture p).inputs name).1).1
        ((lower (a :: b :: cs)).eval CommonNominalFullCarrier.model m) ∧
      Equivalent (m ((capture p).inputs name).2).1
        ((upper (a :: b :: cs)).eval CommonNominalFullCarrier.model m) := by
  have generated : All CommonNominalFullCarrier.model m
      (equations ((capture p).inputs name).1 (lower (a :: b :: cs)) ++
        equations ((capture p).inputs name).2 (upper (a :: b :: cs))) := by
    intro atom member
    apply held atom
    apply List.mem_flatMap.mpr
    exact ⟨name,named,by simpa [seen, capture, frame] using member⟩
  have split := (PresenceNormalForm.all_append ..).mp generated
  exact ⟨(equations_exact ..).mp split.1,(equations_exact ..).mp split.2⟩

theorem lower_cut (p : Packet roles) (m : Assignment) (name : Nat)
    (named : name ∈ p.declaration.inputNames) (held : merged p m)
    (nonempty : occurs p name ≠ []) (value : Ty) :
    Subtype (m ((capture p).inputs name).1).1 value ↔
      ∀ bounds ∈ occurs p name, Subtype (m bounds.1).1 value := by
  cases seen : occurs p name with
  | nil => exact False.elim (nonempty seen)
  | cons a rest =>
    cases rest with
    | nil =>
      have same : (capture p).inputs name = a :=
        GeneralNominalVersionedAllocation231.singleton_input seen
      simp [same]
    | cons b cs =>
      have aggregate := (equations_of_many p m name named held seen).1
      exact ⟨fun below => (lower_exact m _ (by simp) value).mp (subtype_trans aggregate.2 below),
        fun all => subtype_trans aggregate.1 ((lower_exact m _ (by simp) value).mpr all)⟩

theorem upper_cut (p : Packet roles) (m : Assignment) (name : Nat)
    (named : name ∈ p.declaration.inputNames) (held : merged p m)
    (nonempty : occurs p name ≠ []) (value : Ty) :
    Subtype value (m ((capture p).inputs name).2).1 ↔
      ∀ bounds ∈ occurs p name, Subtype value (m bounds.2).1 := by
  cases seen : occurs p name with
  | nil => exact False.elim (nonempty seen)
  | cons a rest =>
    cases rest with
    | nil =>
      have same : (capture p).inputs name = a :=
        GeneralNominalVersionedAllocation231.singleton_input seen
      simp [same]
    | cons b cs =>
      have aggregate := (equations_of_many p m name named held seen).2
      exact ⟨fun above => (upper_exact m _ (by simp) value).mp (subtype_trans above aggregate.1),
        fun all => subtype_trans ((upper_exact m _ (by simp) value).mpr all) aggregate.2⟩

def LowerSame (p q : Packet roles) (m : Assignment) (name : Nat) : Prop :=
  ∀ target : Ty,
    (∀ bounds ∈ occurs p name, Subtype (m bounds.1).1 target) ↔
    (∀ bounds ∈ occurs q name, Subtype (m bounds.1).1 target)

def UpperSame (p q : Packet roles) (m : Assignment) (name : Nat) : Prop :=
  ∀ target : Ty,
    (∀ bounds ∈ occurs p name, Subtype target (m bounds.2).1) ↔
    (∀ bounds ∈ occurs q name, Subtype target (m bounds.2).1)

theorem lower_equivalent (p q : Packet roles) (m : Assignment) (name : Nat)
    (pn : name ∈ p.declaration.inputNames) (qn : name ∈ q.declaration.inputNames)
    (pm : merged p m) (qm : merged q m) (pe : occurs p name ≠ []) (qe : occurs q name ≠ []) :
    Equivalent (m ((capture p).inputs name).1).1 (m ((capture q).inputs name).1).1 ↔
    LowerSame p q m name := by
  have eqv : LowerSame p q m name ↔ ∀ target : Ty,
      Subtype (m ((capture p).inputs name).1).1 target ↔ Subtype (m ((capture q).inputs name).1).1 target := by
    constructor <;> intro h target
    · exact (lower_cut p m name pn pm pe target).trans ((h target).trans (lower_cut q m name qn qm qe target).symm)
    · exact (lower_cut p m name pn pm pe target).symm.trans ((h target).trans (lower_cut q m name qn qm qe target))
  rw [eqv]
  constructor
  · intro same t
    exact ⟨subtype_trans same.2, subtype_trans same.1⟩
  · intro same
    exact ⟨(same _).mpr (subtype_refl _), (same _).mp (subtype_refl _)⟩

theorem upper_equivalent (p q : Packet roles) (m : Assignment) (name : Nat)
    (pn : name ∈ p.declaration.inputNames) (qn : name ∈ q.declaration.inputNames)
    (pm : merged p m) (qm : merged q m) (pe : occurs p name ≠ []) (qe : occurs q name ≠ []) :
    Equivalent (m ((capture p).inputs name).2).1 (m ((capture q).inputs name).2).1 ↔
    UpperSame p q m name := by
  have eqv : UpperSame p q m name ↔ ∀ target : Ty,
      Subtype target (m ((capture p).inputs name).2).1 ↔ Subtype target (m ((capture q).inputs name).2).1 := by
    constructor <;> intro h target
    · exact (upper_cut p m name pn pm pe target).trans ((h target).trans (upper_cut q m name qn qm qe target).symm)
    · exact (upper_cut p m name pn pm pe target).symm.trans ((h target).trans (upper_cut q m name qn qm qe target))
  rw [eqv]
  constructor
  · intro same t
    exact ⟨fun a => subtype_trans a same.1,fun b => subtype_trans b same.2⟩
  · intro same
    exact ⟨(same _).mp (subtype_refl _),(same _).mpr (subtype_refl _)⟩

end Yulang.GeneralVersionedEndpointCuts315
