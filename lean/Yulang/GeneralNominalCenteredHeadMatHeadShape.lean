import Yulang.GeneralNominalCenteredHeadMatRecordProjection

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatHeadShape
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalFiniteHeadInversion
open GeneralNominalCenteredHeadMatPatternSemantics
open CommonNominalFullCarrier
variable {test : Test}

theorem holds_congr (equal : Equivalent first last) (valid : test.Holds first) : test.Holds last := by
  cases test with
  | scalar => exact eqv_trans (eqv_symm equal) valid
  | structural | nominal =>
      obtain ⟨values,length,known⟩ := valid
      exact ⟨values,length,eqv_trans (eqv_symm equal) known⟩

theorem equivalent_probe (equal : Equivalent first last) (depth rank env obs) :
    CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth first) obs ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env (observeTy depth last) obs :=
  ⟨(CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.2 depth) rank env obs,
    (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 depth) rank env obs⟩

theorem holds_role (valid : test.Holds value) (env : CommonNominalFullDemand.Environment Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe 0 env (observeTy 0 value) (.role 0) ↔ head test ∈ env.roles 0 := by
  cases test with
  | scalar base => exact equivalent_probe valid 0 0 env (.role 0)
  | nominal name count =>
      obtain ⟨arguments,length,equal⟩ := valid
      have same := equivalent_probe equal 0 0 env (.role 0)
      simpa [observe_nominal,CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,
        CommonNominalFullDemand.MaskedProbeStep,length,head] using same
  | structural shape =>
      obtain ⟨values,length,equal⟩ := valid
      have rebuild : List.ofFn (fun index : Fin shape.arity => values[index.val]'(by rw [length]; exact index.isLt)) = values := by
        apply List.ext_getElem
        · simpa only [List.length_ofFn] using length.symm
        · intro index one two; simp only [List.getElem_ofFn]
      have same := build_role (.structural shape)
        (fun index => values[index.val]'(by rw [length]; exact index.isLt)) env
      change CommonNominalFullDemand.ProbeAt _ _ _ (observeTy 0 (shapeValue shape _)) _ ↔ _ at same
      simp only [arity] at same
      rw [rebuild] at same
      exact (equivalent_probe equal 0 0 env (.role 0)).trans same

theorem bottom_no_head (test : Test) : ¬ test.Holds (.bottom : Ty) := by
  intro valid
  have bad := (holds_role valid ⟨fun _ => .bottom,fun _ => []⟩).mp (by trivial)
  cases bad

theorem holds_build (one : TestCanonical first) (two : TestCanonical last)
    (valid : first.Holds (build last values)) : first = last := by
  have heads : head last = head first := by
    let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [head first]⟩
    exact List.mem_singleton.mp ((build_role last values env).mp
      ((holds_role valid env).mpr (List.mem_singleton_self _)))
  cases first with
  | scalar base =>
      exact (test_equal last (.scalar base) values Fin.elim0 two one valid).symm
  | nominal name count =>
      cases last with
      | scalar => cases heads
      | structural shape => cases shape <;> cases heads
      | nominal other length =>
          obtain ⟨rfl,rfl⟩ := CommonNominalFullDemand.Head.nominal.inj heads
          rfl
  | structural shape =>
      obtain ⟨xs,length,equal⟩ := valid
      have rebuild : List.ofFn (fun index : Fin shape.arity => xs[index.val]'(by rw [length]; exact index.isLt)) = xs := by
        apply List.ext_getElem
        · simpa only [List.length_ofFn] using length.symm
        · intro index one two; simp only [List.getElem_ofFn]
      apply Eq.symm
      apply test_equal last (.structural shape) values
        (fun index => xs[index.val]'(by rw [length]; exact index.isLt)) two one
      simpa only [build,arity,rebuild] using equal

theorem record_head (valid : test.Holds (record label payload tail)) :
    ∃ keys, test = .structural (.record keys) := by
  have heads : head test = .records := by
    let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [.records]⟩
    exact List.mem_singleton.mp ((holds_role valid env).mp (by exact List.mem_singleton_self _))
  cases test with
  | scalar | nominal => cases heads
  | structural shape =>
      cases shape with
      | pair | variant => cases heads
      | record keys => exact ⟨keys,rfl⟩
      | exactEmpty =>
          obtain ⟨values,_,equal⟩ := valid
          have seen : CommonNominalFullDemand.ProbeAt Common.rowLe 0
              ⟨fun _ => .bottom,fun _ => []⟩ (observeTy 0 (record label payload tail)) (.field label .trivial) := by
            change CommonNominalFullDemand.ProbeAt _ _ _ (.record label _ _) _
            rw [CommonNominalFullDemand.probeAt_record_field,ite_eq_left rfl]
            exact CommonNominalFullDemand.probeAt_trivial ..
          exact False.elim ((equivalent_probe equal 0 0 ⟨fun _ => .bottom,fun _ => []⟩ (.field label .trivial)).mp seen)

end Yulang.GeneralNominalCenteredHeadMatHeadShape
