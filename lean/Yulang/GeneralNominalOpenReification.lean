import Yulang.GeneralNominalOpenPatternLabels

/-! Open projections retain their original source Pattern keys, including
variable children of variants and sorted record payloads. -/
namespace Yulang.GeneralNominalOpenReification
open GeneralDeclarationPatterns GeneralNominalInspection
open GeneralNominalOriginTerms GeneralNominalCompoundReadback GeneralNominalSourcePatternParts
open GeneralNominalOpenPatternLabels GeneralNominalFiniteMeaning

theorem child_source (pattern : Pattern) (covered : GeneralDeclarationPatterns.covered pattern = true)
    (present : child ∈ queryChildren (translate constructors interpretation pattern)) :
    ∃ part, Part pattern part ∧ translate constructors interpretation part = child := by
  cases pattern with
  | var | join => simp only [translate,queryChildren,List.not_mem_nil] at present
  | variant tag payload =>
    rw [GeneralNominalTemplateSubstitution.variant_query payload covered] at present
    exact ⟨payload,.variant .refl,(List.mem_singleton.mp present).symm⟩
  | app key arguments =>
    rw [translate.eq_def] at present
    dsimp only at present
    split at present
    · cases present
    · cases present
    · cases present
    · simp only [queryChildren,List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with one | two
      · exact ⟨_,.argument (List.mem_cons_self ..) .refl,one.symm⟩
      · exact ⟨_,.argument (List.mem_cons_of_mem _ (List.mem_singleton_self _)) .refl,two.symm⟩
    · split at present
      · split at present
        · obtain ⟨part,_,equal⟩ := List.mem_map.mp present
          exact ⟨part.val,.argument part.property .refl,equal⟩
        · cases present
      · cases present
  | record label payload tail =>
    simp only [translate] at present
    split at present
    · rename_i labels children tailQuery
      obtain ⟨field,member,equal⟩ := List.mem_map.mp present
      have member := List.mem_mergeSort.mp member
      rcases List.mem_cons.mp member with first | later
      · subst field
        exact ⟨payload,.payload .refl,equal⟩
      · have childMember : child ∈ children := equal ▸ (List.of_mem_zip later).2
        have nested : child ∈ queryChildren (translate constructors interpretation tail) := by
          rw [tailQuery]; exact childMember
        obtain ⟨part,path,translated⟩ := child_source tail ((Bool.and_eq_true ..).mp covered).2 nested
        exact ⟨part,.tail path,translated⟩
    · cases present
  termination_by sizeOf pattern

theorem part_covered (part : Part pattern child) (covered : GeneralDeclarationPatterns.covered pattern = true) :
    GeneralDeclarationPatterns.covered child = true := by
  induction part with
  | refl => exact covered
  | argument member part ih => exact ih (GeneralNominalChildAssembly.covered_member _ covered _ member)
  | payload part ih => exact ih ((Bool.and_eq_true ..).mp covered).1
  | tail part ih => exact ih ((Bool.and_eq_true ..).mp covered).2
  | variant part ih => exact ih covered
  | first | last => cases covered

theorem child_source_label (known : Label context pattern (.node test children)) (index : Fin (arity test)) :
    ∃ source, Part pattern source ∧ Label context source (children index) := by
  obtain ⟨source,part,translated⟩ := child_source pattern known.1 (child := quote (children index)) (by
    rw [known.2.1]
    cases test with
    | scalar => exact Fin.elim0 index
    | structural | nominal => exact List.mem_ofFn.mpr ⟨index,rfl⟩)
  exact ⟨source,part,part_covered part known.1,translated,known.2.2.2 index⟩

theorem followed_source_label (path : Follows root term endpoint part) (known : Label context pattern term) :
    ∃ source, Part pattern source ∧ Label context source part := by
  induction path with
  | root => exact ⟨pattern,.refl,known⟩
  | child test children index prior ih =>
    obtain ⟨source,member,meaning⟩ := ih
    obtain ⟨sub,subpart,label⟩ := child_source_label meaning index
    exact ⟨sub,part_trans member subpart,label⟩

end Yulang.GeneralNominalOpenReification
