import Yulang.GeneralDictionaryCountedRoot216
import Yulang.GeneralNominalCenteredHeadMatInspectionSemantics

/-! Record-spine brackets retain arbitrary terminal tails. The lower finite
record excludes unlimited field/optional observations before regularization. -/
namespace Yulang.GeneralDictionaryRecordBracket216
open CommonNominalFullCarrier GeneralNominalCenteredHeadMatRecordReadback
open GeneralNominalStructuralReadback (recordValues)
open GeneralNominalRecordInversion

variable {fields : List (Nat × Ty)}

theorem empty_tail_of_lower (below : Subtype (recordValues lower) (fold fields rest))
    (cases : NoFields rest ∨ AllFields rest) : NoFields rest := by
  rcases cases with empty | full
  · exact empty
  · let label := (fields.map Prod.fst ++ lower.map Prod.fst).foldr Nat.max 0 + 1
    have beyond : ∀ x ∈ fields.map Prod.fst ++ lower.map Prod.fst, x < label := by
      intro x member
      exact Nat.lt_succ_of_le (GeneralNominalAllocation.member_le_max _ x member)
    have one : label ∉ fields.map Prod.fst := by intro h; exact Nat.lt_irrefl _ (beyond _ (List.mem_append_left _ h))
    have two : label ∉ lower.map Prod.fst := by intro h; exact Nat.lt_irrefl _ (beyond _ (List.mem_append_right _ h))
    have seen := (fold_absent (rest := rest) one).mpr (full label)
    have moved := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.field label .trivial) seen
    exact False.elim (two ((field_presence lower label).mp moved))

theorem fold_optional_present (unique : (fields.map Prod.fst).Nodup)
    (member : (label,value) ∈ fields) :
    CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth (fold fields rest)) (.optional label obs) ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env
        (CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node value)) obs := by
  induction fields with
  | nil => cases member
  | cons field fields ih =>
      rcases List.mem_cons.mp member with equal | member
      · cases equal
        change CommonNominalFullDemand.ProbeAt _ _ _ (.record label _ _) _ ↔ _
        rw [CommonNominalFullDemand.probeAt_record_optional,ite_eq_left rfl]
      · have different : label ≠ field.1 := by
          intro same
          exact (List.nodup_cons.mp unique).1 (same ▸ List.mem_map.mpr ⟨(label,value),member,rfl⟩)
        change CommonNominalFullDemand.ProbeAt _ _ _ (.record field.1 _ _) _ ↔ _
        rw [CommonNominalFullDemand.probeAt_record_optional,ite_eq_right different]
        change (CommonNominalFullDemand.ProbeAt _ rank env (observeTy depth (fold fields rest)) (.optional label obs) ∨ obs = .trivial) ↔ _
        rw [ih (List.nodup_cons.mp unique).2 member]
        constructor
        · intro h; rcases h with h | h
          · exact h
          · subst obs; exact CommonNominalFullDemand.probeAt_trivial ..
        · exact Or.inl

theorem fold_optional_absent (nonempty : fields ≠ []) (absent : label ∉ fields.map Prod.fst) :
    CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth (fold fields rest)) (.optional label obs) ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth rest) (.optional label obs) ∨ obs = .trivial := by
  induction fields with
  | nil => exact False.elim (nonempty rfl)
  | cons field fields ih =>
      have different : label ≠ field.1 := fun same => absent (List.mem_cons.mpr (Or.inl same))
      have absentTail : label ∉ fields.map Prod.fst := fun h => absent (List.mem_cons_of_mem _ h)
      change CommonNominalFullDemand.ProbeAt _ _ _ (.record field.1 _ _) _ ↔ _
      rw [CommonNominalFullDemand.probeAt_record_optional,ite_eq_right different]
      cases fields with
      | nil => rfl
      | cons field tail =>
          change (CommonNominalFullDemand.ProbeAt _ rank env (observeTy depth (fold (field::tail) rest)) (.optional label obs) ∨ obs = .trivial) ↔ _
          rw [ih (by simp) absentTail]
          constructor
          · intro h; rcases h with (h | h) | h
            · exact Or.inl h
            · exact Or.inr h
            · exact Or.inr h
          · exact Or.inl

theorem record_optional_absent (absent : label ∉ lower.map Prod.fst)
    (seen : CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth (recordValues lower)) (.optional label obs)) : obs = .trivial := by
  cases lower with
  | nil => cases rank <;> exact seen
  | cons entry tail =>
      have result := (fold_optional_absent (fields := entry::tail) (rest := emptyRecord) (by simp) absent).mp seen
      rcases result with impossible | equal
      · cases rank <;> exact impossible
      · exact equal

theorem regularize (nonempty : fields ≠ []) (unique : (fields.map Prod.fst).Nodup)
    (empty : NoFields rest) (same : ∀ label, label ∈ fields.map Prod.fst ↔ label ∈ lower.map Prod.fst)
    (below : Subtype (recordValues lower) (fold fields rest)) :
    Equivalent (fold fields rest) (recordValues fields) := by
  have probes (depth rank : Nat) (env : CommonNominalFullDemand.Environment Row) (obs : CommonNominalFullDemand.Observation Row) :
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth (fold fields rest)) obs ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth (recordValues fields)) obs := by
    cases fields with
    | nil => exact False.elim (nonempty rfl)
    | cons entry tail =>
      cases obs <;> try (cases rank <;> rfl)
      case field label inner =>
        by_cases present : label ∈ (entry::tail).map Prod.fst
        · obtain ⟨pair,member,equal⟩ := List.mem_map.mp present
          subst label
          exact (fold_field unique member).trans (fold_field (rest := emptyRecord) unique member).symm
        · change CommonNominalFullDemand.ProbeAt _ rank env (observeTy depth (fold (entry::tail) rest)) (.field label inner) ↔ CommonNominalFullDemand.ProbeAt _ rank env (observeTy depth (fold (entry::tail) emptyRecord)) (.field label inner)
          rw [fold_absent present,fold_absent (rest := emptyRecord) present]
          have missing := empty depth rank env label inner
          cases rank <;> exact iff_false_intro missing
      case optional label inner =>
        by_cases present : label ∈ (entry::tail).map Prod.fst
        · obtain ⟨pair,member,equal⟩ := List.mem_map.mp present
          subst label
          exact (fold_optional_present unique member).trans (fold_optional_present (rest := emptyRecord) unique member).symm
        · have absent : label ∉ lower.map Prod.fst := fun member => present ((same label).mpr member)
          constructor
          · intro accepted
            have moved := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below depth) rank env (.optional label inner) accepted
            have trivial := record_optional_absent absent moved
            exact (fold_optional_absent (fields := entry::tail) (rest := emptyRecord) (by simp) present).mpr (Or.inr trivial)
          · intro accepted
            have trivial := record_optional_absent present accepted
            exact (fold_optional_absent (fields := entry::tail) (rest := rest) (by simp) present).mpr (Or.inr trivial)
  constructor <;> intro depth <;> apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr <;> intro rank env obs accepted
  · exact (probes depth rank env obs).mpr accepted
  · exact (probes depth rank env obs).mp accepted

theorem signature (unique : (fields.map Prod.fst).Nodup) (empty : NoFields rest)
    (same : lower.map Prod.fst = upper.map Prod.fst)
    (below : Subtype (recordValues lower) (fold fields rest))
    (above : Subtype (fold fields rest) (recordValues upper)) :
    ∀ label, label ∈ fields.map Prod.fst ↔ label ∈ lower.map Prod.fst := by
  intro label
  have source := fold_presence (env := ⟨fun _ => .bottom,fun _ => []⟩) (label := label) empty unique
  constructor
  · intro member
    exact (field_presence lower label).mp
      ((CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 _ _ (source.mpr member))
  · intro member
    rw [same] at member
    exact source.mp
      ((CommonNominalFullDemand.producerLe_iff_probe _ _).mp (above 0) 0 _ _ ((field_presence upper label).mpr member))

theorem bracket (nonempty : fields ≠ []) (unique : (fields.map Prod.fst).Nodup)
    (cases : NoFields rest ∨ AllFields rest)
    (ordered : keys.Pairwise (· < ·))
    (llen : lower.length = keys.length) (ulen : upper.length = keys.length)
    (below : Subtype (recordValues (keys.zip lower)) (fold fields rest))
    (above : Subtype (fold fields rest) (recordValues (keys.zip upper))) :
    ∃ values, values.length = keys.length ∧
      Equivalent (fold fields rest) (GeneralNominalRecursiveInspection.shapeValue (.record keys) values) := by
  have empty := empty_tail_of_lower below cases
  have same := signature unique empty
    (by rw [List.map_fst_zip (Nat.le_of_eq llen.symm),List.map_fst_zip (Nat.le_of_eq ulen.symm)]) below above
  have regular := regularize nonempty unique empty same below
  let sorted := fields.mergeSort (fun first last => first.1 ≤ last.1)
  have perm : sorted.Perm fields := List.mergeSort_perm .. 
  have members : ∀ label, label ∈ sorted.map Prod.fst ↔ label ∈ keys := by
    intro label
    rw [(perm.map Prod.fst).mem_iff,same label,List.map_fst_zip (Nat.le_of_eq llen.symm)]
  have ord : (sorted.map Prod.fst).Pairwise (· ≤ ·) := by
    apply (List.pairwise_map ..).mpr
    have h := List.pairwise_mergeSort (le := fun first last : Nat × Ty => decide (first.1 ≤ last.1))
      (by intro a b c one two; exact decide_eq_true (Nat.le_trans (of_decide_eq_true one) (of_decide_eq_true two)))
      (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact Nat.le_total ..) fields
    simpa only [sorted,decide_eq_true_eq] using h
  have names : sorted.map Prod.fst = keys :=
    List.Perm.eq_of_pairwise (le := Nat.le) (fun _ _ _ _ one two => Nat.le_antisymm one two)
      ord (ordered.imp (fun h => Nat.le_of_lt h))
      ((List.perm_ext_iff_of_nodup ((perm.map Prod.fst).nodup_iff.mpr unique)
        (ordered.imp (fun h => Nat.ne_of_lt h))).mpr members)
  refine ⟨sorted.map Prod.snd,?_,?_⟩
  · simpa only [List.length_map] using congrArg List.length names
  · have reordered := GeneralNominalCenteredHeadMatInspectionSemantics.record_permutation perm.symm unique
    have zipped : (sorted.map Prod.fst).zip (sorted.map Prod.snd) = sorted := by
      induction sorted with
      | nil => rfl
      | cons a tail ih => simp only [List.map_cons,List.zip_cons_cons,ih]
    rw [GeneralNominalRecordInversion.record_shape _ _ (by simpa only [List.length_map] using congrArg List.length names),
      ← names,zipped]
    exact GeneralNominalCenteredHeadMatPatternSemantics.eqv_trans regular reordered

end Yulang.GeneralDictionaryRecordBracket216
