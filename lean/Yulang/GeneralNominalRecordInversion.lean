import Yulang.GeneralNominalClosedPatternMass

/-! Canonical record signatures and variant tags are recovered from actual
carrier equivalence before their projection positions are compared. -/
namespace Yulang.GeneralNominalRecordInversion
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalStructuralReadback
open GeneralNormalizedObservation (Shape recordTerm)
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

set_option backward.isDefEq.respectTransparency false in
theorem record_shape (labels : List Nat) (values : List Ty) (length : values.length = labels.length) :
    shapeValue (.record labels) values = recordValues (labels.zip values) := by
  have evalFields (fields : List (Nat × TyTerm (Fin labels.length))) :
      (recordTerm fields .emptyRecord).eval CommonNominalFullCarrier.model
        (fun index => ((values[index.val]?).getD .bottom,Common.rowEmpty)) =
      recordValues (fields.map fun field => (field.1,field.2.eval CommonNominalFullCarrier.model
        (fun index => ((values[index.val]?).getD .bottom,Common.rowEmpty)))) := by
    induction fields with
    | nil => rfl
    | cons field rest ih =>
      change record field.1 _ ((recordTerm rest .emptyRecord).eval CommonNominalFullCarrier.model
        (fun index => ((values[index.val]?).getD .bottom,Common.rowEmpty))) = _
      rw [ih]; rfl
  simp only [shapeValue,Shape.term]
  erw [evalFields]
  rw [List.map_ofFn]
  congr 1
  apply List.ext_getElem
  · simp [length]
  · intro index first last
    have bound : index < values.length := by simpa only [List.length_ofFn,← length] using first
    simp only [List.getElem_ofFn,List.getElem_zip,Function.comp_def,TyTerm.eval,List.getElem?_eq_getElem bound,Option.getD_some]
    rfl

theorem field_presence (fields : List (Nat × Ty)) (label : Nat) :
    CommonNominalFullDemand.ProbeAt Common.rowLe 0 ⟨fun _ => .bottom,fun _ => []⟩
      (observeTy 0 (recordValues fields)) (.field label .trivial) ↔ label ∈ fields.map Prod.fst := by
  induction fields with
  | nil => change False ↔ label ∈ ([] : List Nat); simp
  | cons field rest ih =>
    change CommonNominalFullDemand.ProbeAt _ _ _
      (.record field.1 _ (observeTy 0 (recordValues rest))) _ ↔ _
    rw [CommonNominalFullDemand.probeAt_record_field]
    simp only [CommonNominalFullDemand.probeAt_trivial,List.map_cons,List.mem_cons]
    by_cases same : label = field.1 <;> simp [same,ih]

theorem record_membership (first last : List (Nat × Ty))
    (equal : Equivalent (recordValues first) (recordValues last)) (label : Nat) :
    label ∈ first.map Prod.fst ↔ label ∈ last.map Prod.fst := by
  constructor
  · intro member
    apply (field_presence last label).mp
    exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.2 0) 0 _ _
      ((field_presence first label).mpr member)
  · intro member
    apply (field_presence first label).mp
    exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0 _ _
      ((field_presence last label).mpr member)

theorem record_signatures (first last : List Nat) (xs ys : List Ty)
    (one : first.Pairwise (· < ·)) (two : last.Pairwise (· < ·))
    (xlen : xs.length = first.length) (ylen : ys.length = last.length)
    (equal : Equivalent (shapeValue (.record first) xs) (shapeValue (.record last) ys)) : first = last := by
  rw [record_shape first xs xlen,record_shape last ys ylen] at equal
  have members : ∀ label, label ∈ first ↔ label ∈ last := by
    intro label
    simpa only [List.map_fst_zip (Nat.le_of_eq xlen.symm),List.map_fst_zip (Nat.le_of_eq ylen.symm)] using
      record_membership (first.zip xs) (last.zip ys) equal label
  have permutation := (List.perm_ext_iff_of_nodup (one.imp (fun less => Nat.ne_of_lt less))
    (two.imp (fun less => Nat.ne_of_lt less))).mpr members
  exact List.Perm.eq_of_pairwise (le := Nat.le) (fun _ _ _ _ a b => Nat.le_antisymm a b)
    (one.imp (fun less => Nat.le_of_lt less)) (two.imp (fun less => Nat.le_of_lt less)) permutation

variable {model : GeneralNominalCommonBridge.Assignment}

theorem record_projection (labels readLabels : List Nat) (values : Fin labels.length → Ty)
    (canonical : labels.Pairwise (· < ·)) (readCanonical : readLabels.Pairwise (· < ·))
    (known : At model .actual root (build (.structural (.record labels)) values))
    (observed : Observes model (.structural root (.record readLabels) index) actual) :
    ∃ position : Fin labels.length, position.val = index ∧ readLabels = labels ∧ Equivalent actual (values position) := by
  cases observed with
  | structural seen length equal found =>
    have parent := known.2 _ seen
    have same := record_signatures readLabels labels _ (List.ofFn values) readCanonical canonical length
      (List.length_ofFn ..) ⟨subtype_trans equal.2 parent.1,subtype_trans parent.2 equal.1⟩
    subst readLabels
    have bound : index < labels.length := by
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simpa only [length,Shape.arity] using bound
    let position : Fin labels.length := ⟨index,bound⟩
    have projected := project_value (.structural (.record labels)) canonical values known position
    exact ⟨position,rfl,rfl,projected.2 _ (.structural seen length equal found)⟩

theorem variant_tags (first last : Nat) (a b : Ty) (equal : Equivalent (variant first a) (variant last b)) :
    first = last := by
  have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.variant last .trivial) (by exact ⟨rfl,trivial⟩)
  exact accepted.1

theorem variant_projection (tag readTag : Nat) (value : Ty)
    (known : At model .actual root (variant tag value))
    (observed : Observes model (.structural root (.variant readTag) index) actual) :
    readTag = tag ∧ index = 0 ∧ Equivalent actual value := by
  cases observed with
  | structural seen length equal found =>
    obtain ⟨child,rfl⟩ := List.length_eq_one_iff.mp length
    have parent := known.2 _ seen
    have tags := variant_tags readTag tag child value
      ⟨subtype_trans equal.2 parent.1,subtype_trans parent.2 equal.1⟩
    subst readTag
    cases index with
    | succ index => cases found
    | zero =>
      cases Option.some.inj found
      exact ⟨rfl,rfl,(common_variant_iff tag _ _).mp (subtype_trans equal.2 parent.1),
        (common_variant_iff tag _ _).mp (subtype_trans parent.2 equal.1)⟩

end Yulang.GeneralNominalRecordInversion
