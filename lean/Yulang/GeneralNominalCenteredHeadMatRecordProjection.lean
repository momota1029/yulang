import Yulang.GeneralNominalCenteredHeadMatRecordReadback

set_option backward.isDefEq.respectTransparency false

/-! Each demanded record position has a finite source payload. Sorting changes
the order of these payloads and preserves their total structural size. -/
namespace Yulang.GeneralNominalCenteredHeadMatRecordProjection
open GeneralDeclarationPatterns GeneralPatternNormalForm
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatRecordReadback
open GeneralNominalStructuralReadback (recordValues)
open CommonNominalFullCarrier

theorem fold_payload (first last : List (Nat × Ty)) (rest : Ty)
    (one : (first.map Prod.fst).Nodup) (two : (last.map Prod.fst).Nodup)
    (member : (label,a) ∈ first) (present : (label,b) ∈ last)
    (equal : Equivalent (fold first rest) (recordValues last)) : Equivalent a b := by
  constructor <;> intro depth <;>
    apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr <;> intro rank env obs accepted
  · have seen := (fold_field (depth := depth+1) two present (rest := emptyRecord)).mpr accepted
    have moved := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 (depth+1)) rank env (.field label obs) seen
    exact (fold_field one member).mp moved
  · have seen := (fold_field (depth := depth+1) one member (rest := rest)).mpr accepted
    have moved := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.2 (depth+1)) rank env (.field label obs) seen
    exact (fold_field two present).mp moved

def sorted (pattern : Pattern) : List (Nat × Pattern) :=
  (entries pattern).mergeSort (fun first last => first.1 ≤ last.1)

theorem sorted_order (pattern : Pattern) : ((sorted pattern).map Prod.fst).Pairwise (· ≤ ·) := by
  apply (List.pairwise_map ..).mpr
  have sortedProof := List.pairwise_mergeSort (le := fun first last : Nat × Pattern => decide (first.1 ≤ last.1))
    (by intro a b c one two; exact decide_eq_true (Nat.le_trans (of_decide_eq_true one) (of_decide_eq_true two)))
    (by intro a b; simp only [Bool.or_eq_true,decide_eq_true_eq]; exact Nat.le_total ..) (entries pattern)
  simpa only [sorted,decide_eq_true_eq] using sortedProof

theorem sorted_labels
    (closed : pattern.variables = []) (normal : Normal pattern)
    (length : values.length = keys.length) (ordered : keys.Pairwise (· < ·))
    (equal : Equivalent (eval (algebra constructors interpretation) variables pattern)
      (GeneralNominalRecursiveInspection.shapeValue (.record keys) values)) :
    (sorted pattern).map Prod.fst = keys := by
  have unique : ((entries pattern).map Prod.fst).Nodup := by
    rw [labels_entries]; exact fields_unique pattern normal
  let evaluated := (entries pattern).map fun field => (field.1,eval (algebra constructors interpretation) variables field.2)
  have evaluatedUnique : (evaluated.map Prod.fst).Nodup := by
    simpa only [evaluated,List.map_map,Function.comp_def] using unique
  rw [eval_fold pattern,GeneralNominalRecordInversion.record_shape keys values length] at equal
  have empty := empty_tail_of_finite equal
    (terminal_fields (tail pattern) (tail_closed pattern closed) (tail_normal pattern normal) (tail_not_record pattern))
  have members (label : Nat) : label ∈ (entries pattern).map Prod.fst ↔ label ∈ keys := by
    have source := fold_presence (env := ⟨fun _ => .bottom,fun _ => []⟩) (label := label) empty evaluatedUnique
    have target := GeneralNominalRecordInversion.field_presence (keys.zip values) label
    have same : CommonNominalFullDemand.ProbeAt Common.rowLe 0 ⟨fun _ => .bottom,fun _ => []⟩
        (observeTy 0 (fold evaluated (eval (algebra constructors interpretation) variables (tail pattern)))) (.field label .trivial) ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe 0 ⟨fun _ => .bottom,fun _ => []⟩
        (observeTy 0 (recordValues (keys.zip values))) (.field label .trivial) :=
      ⟨(CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.2 0) 0 _ _,
        (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0 _ _⟩
    simpa only [evaluated,List.map_map,Function.comp_def,List.map_fst_zip (Nat.le_of_eq length.symm)] using
      source.symm.trans (same.trans target)
  have perm := (List.mergeSort_perm (entries pattern) (fun first last => first.1 ≤ last.1)).map Prod.fst
  have equalMembers : ∀ label, label ∈ (sorted pattern).map Prod.fst ↔ label ∈ keys :=
    fun label => perm.mem_iff.trans (members label)
  have permutation := (List.perm_ext_iff_of_nodup (perm.nodup_iff.mpr unique)
    (ordered.imp (fun h => Nat.ne_of_lt h))).mpr equalMembers
  exact List.Perm.eq_of_pairwise (le := Nat.le) (fun _ _ _ _ one two => Nat.le_antisymm one two)
    (sorted_order pattern) (ordered.imp (fun h => Nat.le_of_lt h)) permutation

theorem record_parts
    (closed : pattern.variables = []) (normal : Normal pattern)
    (length : values.length = keys.length) (ordered : keys.Pairwise (· < ·))
    (equal : Equivalent (eval (algebra constructors interpretation) variables pattern)
      (GeneralNominalRecursiveInspection.shapeValue (.record keys) values)) :
    ∃ parts : List Pattern, ∃ size : parts.length = keys.length,
      (∀ index : Fin keys.length,
        (parts[index.val]'(by rw [size]; exact index.isLt)).variables = [] ∧
        Normal (parts[index.val]'(by rw [size]; exact index.isLt)) ∧
        Equivalent (values[index.val]'(by omega))
          (eval (algebra constructors interpretation) variables (parts[index.val]'(by rw [size]; exact index.isLt)))) ∧
      keys.length + 1 + (parts.map fun pattern => pattern.encode.size).sum ≤ pattern.encode.size := by
  have names := sorted_labels closed normal length ordered equal
  have sortedLength : (sorted pattern).length = keys.length := by
    simpa only [List.length_map] using congrArg List.length names
  let parts := (sorted pattern).map Prod.snd
  have partsLength : parts.length = keys.length := by simp only [parts,List.length_map,sortedLength]
  refine ⟨parts,partsLength,?_,?_⟩
  · intro index
    let field := (sorted pattern)[index.val]'(by rw [sortedLength]; exact index.isLt)
    have member : field ∈ entries pattern := List.mem_mergeSort.mp (List.getElem_mem ..)
    have fieldLabel : field.1 = keys[index.val] := by
      have atIndex := congrArg (fun list => list[index.val]?) names
      simpa only [List.getElem?_map,List.getElem?_eq_getElem (by rw [sortedLength]; exact index.isLt),
        List.getElem?_eq_getElem index.isLt,Option.map_some,Option.some.injEq,field] using atIndex
    have partEq : parts[index.val]'(by rw [partsLength]; exact index.isLt) = field.2 := by
      simp only [parts,List.getElem_map,field]
    rw [partEq]
    refine ⟨member_closed member closed,member_normal member normal,?_⟩
    have sourceUnique : (((entries pattern).map fun field => (field.1,eval (algebra constructors interpretation) variables field.2)).map Prod.fst).Nodup := by
      simpa only [List.map_map,Function.comp_def,labels_entries] using fields_unique pattern normal
    have targetUnique : ((keys.zip values).map Prod.fst).Nodup := by
      rw [List.map_fst_zip (Nat.le_of_eq length.symm)]
      exact ordered.imp (fun h => Nat.ne_of_lt h)
    have targetMember : (field.1,values[index.val]'(by omega)) ∈ keys.zip values := by
      rw [fieldLabel]
      exact List.mem_iff_getElem.mpr ⟨index.val,by simp [List.length_zip,length,index.isLt],by simp⟩
    rw [eval_fold pattern,GeneralNominalRecordInversion.record_shape keys values length] at equal
    exact eqv_symm (fold_payload _ _ _ sourceUnique targetUnique
      (List.mem_map.mpr ⟨field,member,rfl⟩) targetMember equal)
  · have perm := List.Perm.map (fun field : Nat × Pattern => field.2.encode.size)
      (List.mergeSort_perm (entries pattern) (fun first last => first.1 ≤ last.1))
    have sums : ((sorted pattern).map fun field => field.2.encode.size).sum =
        ((entries pattern).map fun field => field.2.encode.size).sum := perm.sum_nat
    have sizes := entries_mass pattern
    have len : (entries pattern).length = keys.length := by
      simpa only [sorted,List.length_mergeSort] using sortedLength
    simpa only [parts,List.map_map,Function.comp_def,sums,len] using sizes

end Yulang.GeneralNominalCenteredHeadMatRecordProjection
