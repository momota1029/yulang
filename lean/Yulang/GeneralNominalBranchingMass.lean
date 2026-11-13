import Yulang.GeneralNominalCompoundCapturePaths

/-! Semantic sharing preserves constructor mass for finite scalar, pair and
nominal trees. Repeated captures cannot inflate mass by changing witnesses. -/
namespace Yulang.GeneralNominalBranchingMass
open GeneralNominalBranchingReadback CommonNominalFullCarrier

theorem masses_sum (children : List Tree) : masses children = (children.map Tree.mass).sum := by
  induction children <;> simp_all [masses]

theorem equivalent_mass (first : Tree) : ∀ last : Tree,
    Equivalent first.value last.value → first.mass = last.mass := by
  apply Tree.rec
    (motive_1 := fun first => ∀ last : Tree, Equivalent first.value last.value → first.mass = last.mass)
    (motive_2 := fun children => ∀ first ∈ children, ∀ last : Tree,
      Equivalent first.value last.value → first.mass = last.mass)
  · intro base other equal
    cases other with
    | scalar => rfl
    | pair left right => exact False.elim (scalar_not_pair base left.value right.value equal.1)
    | nominal name children => exact False.elim (GeneralNominalPeelingOrigins.base_not_nominal base name _ equal.1)
  · intro left right leftIH rightIH other equal
    cases other with
    | scalar base => exact False.elim (scalar_not_pair base left.value right.value equal.2)
    | nominal name children => exact False.elim (pair_not_nominal left.value right.value name _ equal.1)
    | pair a b =>
      have one := (common_pair_iff ..).mp equal.1
      have two := (common_pair_iff ..).mp equal.2
      have first := leftIH a ⟨one.1,two.1⟩
      have last := rightIH b ⟨one.2,two.2⟩
      simp only [Tree.mass,first,last]
  · intro name children ih other equal
    cases other with
    | scalar base => exact False.elim (GeneralNominalPeelingOrigins.base_not_nominal base name _ equal.2)
    | pair left right => exact False.elim (nominal_not_pair name _ left.value right.value equal.1)
    | nominal label targets =>
      have same := (nominal_regular_invariant_exact name label (values children) (values targets)).mp equal.1
      have length : children.length = targets.length := by simpa only [values_length] using same.2.1
      have mapped : children.map Tree.mass = targets.map Tree.mass := by
        apply List.ext_getElem (by simp only [List.length_map,length])
        intro index one two
        have left : index < children.length := by simpa only [List.length_map] using one
        have right : index < targets.length := by simpa only [List.length_map] using two
        simp only [List.getElem_map]
        apply ih _ (List.getElem_mem left)
        exact same.2.2 index _ _ (values_at children (List.getElem?_eq_getElem left))
          (values_at targets (List.getElem?_eq_getElem right))
      simp only [Tree.mass,masses_sum,mapped]
  · intro first impossible; cases impossible
  · intro head tail headIH tailIH first member
    rcases List.mem_cons.mp member with rfl | member
    · exact headIH
    · exact tailIH first member

theorem shared_capture_mass {model : GeneralNominalCommonBridge.Assignment}
    {packet : GeneralNominalSaturationState.Packet roles}
    (valid : packet.Holds model) (usable : GeneralNominalSharedCaptures.Usable packet name origin)
    (first last : Tree)
    (one : GeneralNominalStructuralContainment.CaptureValue packet model name first.value)
    (two : GeneralNominalStructuralContainment.CaptureValue packet model name last.value) : first.mass = last.mass := by
  obtain ⟨value,seen⟩ := (usable.2 model valid).1
  have left := (one.2.2 origin usable).2 value seen
  have right := (two.2.2 origin usable).2 value seen
  exact equivalent_mass first last ⟨subtype_trans left.2 right.1,subtype_trans right.2 left.1⟩

end Yulang.GeneralNominalBranchingMass
