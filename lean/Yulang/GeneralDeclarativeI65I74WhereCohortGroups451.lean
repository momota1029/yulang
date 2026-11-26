import Yulang.GeneralDeclarativeI65I74WhereCohortLabelIndependence451

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
open Checker408 (Problem)
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (point)

/-- Only internal class keys, not an order of display or a canonical
source representative. The order of every individual class's original
where occurrences is the literal source order. -/
def classKeys : List Nat → List Nat
  | [] => []
  | x::rest =>
    if x ∈ classKeys rest then classKeys rest else x :: classKeys rest

theorem seen_class_keys_exact451 (xs : List Nat) (k : Nat) :
    k ∈ classKeys xs ↔ k ∈ xs := by
  induction xs generalizing k with
  | nil => rfl
  | cons first rest ih =>
    unfold classKeys
    split
    · rename_i e
      have found := (ih first).mp e
      rw [ih k]
      simp only [List.mem_cons]
      exact ⟨Or.inr,fun h => h.elim (fun same => same ▸ found) id⟩
    · simp only [List.mem_cons,ih]

theorem class_key_list_has_no_repeated_class451 (xs : List Nat) :
    (classKeys xs).Nodup := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    unfold classKeys
    split
    · exact ih
    · rename_i never
      refine .cons (fun y found eq => ?_) ih
      subst y
      exact never found

structure CohortOrigins where
  key : Nat
  marks : List OriginalMark

def OriginalDiagnostic.cohortsWithOrigins {p : Problem} {a : ParentSelection p} (d : OriginalDiagnostic a) :
    List CohortOrigins :=
  (classKeys (d.marks.map OriginalMark.classLabel)).map fun label => ⟨label,d.atClass label⟩

theorem generated_group_has_exact_source_order451 {p : Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) {g : CohortOrigins} (present : g ∈ d.cohortsWithOrigins) :
    g.marks = d.atClass g.key ∧ g.marks ≠ [] ∧ g.marks.Sublist d.marks := by
  obtain ⟨k,seen,h⟩ := List.mem_map.mp present
  cases h
  have marked := (seen_class_keys_exact451 _ _).mp seen
  obtain ⟨m,atMark,label⟩ := List.mem_map.mp marked
  have known : m ∈ d.atClass k := (only_marks_of_selected_class451 d _ _).mpr ⟨atMark,label⟩
  refine ⟨rfl,?_,validated_class_location_list_keeps_source_order451 d _⟩
  intro empty
  change d.atClass k = [] at empty
  rw [empty] at known
  exact List.not_mem_nil known

theorem every_raw_original_occurrence_is_in_exactly_one_group451 {p : Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {m : OriginalMark} (seen : m ∈ d.marks) :
    (∃ g ∈ d.cohortsWithOrigins, m ∈ g.marks) ∧
      ∀ g h, g ∈ d.cohortsWithOrigins → h ∈ d.cohortsWithOrigins →
        m ∈ g.marks → m ∈ h.marks → g = h := by
  refine ⟨?_,?_⟩
  · refine ⟨⟨m.classLabel,d.atClass m.classLabel⟩,?_,
      (only_marks_of_selected_class451 d _ _).mpr ⟨seen,rfl⟩⟩
    exact List.mem_map.mpr ⟨_,(seen_class_keys_exact451 _ _).mpr (List.mem_map.mpr ⟨m,seen,rfl⟩),rfl⟩
  · intro g h whereG whereH inG inH
    obtain ⟨gkey,_,rfl⟩ := List.mem_map.mp whereG
    obtain ⟨hkey,_,rfl⟩ := List.mem_map.mp whereH
    have k1 := (only_marks_of_selected_class451 d _ _).mp inG |>.2
    have k2 := (only_marks_of_selected_class451 d _ _).mp inH |>.2
    rw [←k1,←k2]

theorem ordered_marks_no_fewer_and_no_extra_original_clauses451 {p : Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) :
    d.marks.length = a.decl.requirements.length := by
  have upper : d.marks.length ≤ a.decl.requirements.length := by
    unfold OriginalDiagnostic.marks
    simp only [List.length_zipWith,List.length_zipIdx]
    omega
  apply Nat.le_antisymm upper
  apply Nat.le_of_not_gt
  intro bad
  let i := d.marks.length
  have inside : i < a.decl.requirements.length := bad
  obtain ⟨_,_,_,_,_,_,inMarks,_⟩ := every_actual_clause_has_a_preserved_location_mark451 d
    (List.getElem?_eq_getElem inside)
  have within := (List.getElem?_eq_some_iff.mp inMarks).choose
  omega

theorem any_mark_is_actual_original_diagnostic451 {p : Problem} {a : ParentSelection p}
    (d : OriginalDiagnostic a) {m : OriginalMark} (seen : m ∈ d.marks) :
    a.children[m.ordinal]? = some m.request ∧
      d.cohorts.labelled[m.ordinal]? = some ((m.request.demand.role,m.actualCenter),m.classLabel) ∧
      d.bits[m.ordinal]? = some m.rawK2 := by
  obtain ⟨i,position⟩ := List.mem_iff_getElem?.mp seen
  have enough : i < a.decl.requirements.length :=
    (ordered_marks_no_fewer_and_no_extra_original_clauses451 d) ▸
      (List.getElem?_eq_some_iff.mp position).choose
  let clause := a.decl.requirements[i]
  have authored : a.decl.requirements[i]? = some clause := List.getElem?_eq_getElem enough
  obtain ⟨_,payload,label,bit,_,_,location,_⟩ := every_actual_clause_has_a_preserved_location_mark451 d authored
  have mark := Option.some.inj (position.symm.trans location)
  subst m
  have request := (known_original_clause_has_actual_payload451 a authored)
  obtain ⟨b,n,_,_,_,actual⟩ := request
  let q : I72.Request := ⟨p.root.occurrence ++ [i],⟨clause.role,[point n],[]⟩⟩
  obtain ⟨atPoint,key,got⟩ := d.cohorts.indexed i actual
  obtain ⟨flag,boolean,_⟩ := status_position_is_actual_child451 d.status i actual
  have center : atPoint = (⟨n,rfl⟩ : ActualPoint q) := actual_point_center_unique451 _ _
  have check : d.marks[i]? = some ⟨i,clause.id,q,n,key,flag⟩ := by
    unfold OriginalDiagnostic.marks
    rw [List.getElem?_zipWith,List.getElem?_zipIdx,List.getElem?_zipWith,List.getElem?_zipWith,
      actual,authored,got,boolean,center]
    simp [ActualPoint.tag,q]
  have identity := Option.some.inj (location.symm.trans check)
  rw [identity]
  refine ⟨actual,?_,boolean⟩
  simpa [center,ActualPoint.tag,q] using got

theorem all_original_members_of_each_group_share_actual_raw_K2451 {p : Problem}
    {a : ParentSelection p} (d : OriginalDiagnostic a) {g : CohortOrigins}
    (genuine : g ∈ d.cohortsWithOrigins) {m n : OriginalMark}
    (first : m ∈ g.marks) (last : n ∈ g.marks) : m.rawK2 = n.rawK2 := by
  have members := (generated_group_has_exact_source_order451 d genuine).1
  rw [members] at first last
  obtain ⟨occurrence,role⟩ := (only_marks_of_selected_class451 d _ _).mp first
  obtain ⟨other,role'⟩ := (only_marks_of_selected_class451 d _ _).mp last
  obtain ⟨left,lx,firstBit⟩ := any_mark_is_actual_original_diagnostic451 d occurrence
  obtain ⟨right,ly,lastBit⟩ := any_mark_is_actual_original_diagnostic451 d other
  have same := equal_label_is_same_raw_diagnostic_at_each_original_location451 d left right lx ly
    (role.trans role'.symm)
  exact Option.some.inj (firstBit.symm.trans (same.trans lastBit))

end Yulang.GeneralDeclarativeI65.I72.WhereSites450.OriginalCohorts451
