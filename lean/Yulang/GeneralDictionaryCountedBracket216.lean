import Yulang.GeneralDictionaryRecordBracket216
namespace Yulang.GeneralDictionaryCountedBracket216
open CommonNominalFullCarrier GeneralDeclarationPatterns GeneralPatternNormalForm
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalRecursiveInspection GeneralNominalFiniteHeadInversion
open GeneralDictionaryInspectionHeads215 GeneralDictionaryCountedRoot216
open GeneralNominalCenteredHeadMatRecordReadback GeneralNominalRecordInversion
open GeneralNominalStructuralReadback (recordValues)

theorem shape_bracket (shape middle : GeneralNormalizedObservation.Shape)
    (canonical : shape.Canonical) (middleCanonical : middle.Canonical)
    (xlen : xs.length = shape.arity) (ylen : ys.length = middle.arity) (zlen : zs.length = shape.arity)
    (below : Subtype (shapeValue shape xs) (shapeValue middle ys))
    (above : Subtype (shapeValue middle ys) (shapeValue shape zs)) : shape = middle := by
  have build (shape : GeneralNormalizedObservation.Shape) (values : List Ty) (len : values.length = shape.arity) :
      shapeValue shape values = GeneralNominalFiniteMeaning.build (.structural shape)
        (fun index => values[index.val]'(by have h : index.val < shape.arity := index.isLt; omega)) := by
    change shapeValue shape values = shapeValue shape _
    congr 1
    apply List.ext_getElem
    · simp [len,GeneralNominalOriginTerms.arity]
    · intro index h1 h2
      simp
  rw [build shape xs xlen,build middle ys ylen] at below
  rw [build middle ys ylen,build shape zs zlen] at above
  exact Test.structural.inj (GeneralNominalFiniteBracket.test_bracket _ _ _ _ _
    canonical middleCanonical below above)

theorem structural (closed : pattern.variables = []) (normal : Normal pattern)
    (canonical : shape.Canonical)
    (xlen : xs.length = shape.arity) (zlen : zs.length = shape.arity)
    (below : Subtype (shapeValue shape xs) (eval (algebra constructors interpretation) (fun _ => .bottom) pattern))
    (above : Subtype (eval (algebra constructors interpretation) (fun _ => .bottom) pattern) (shapeValue shape zs)) :
    (Test.structural shape).Holds (eval (algebra constructors interpretation) (fun _ => .bottom) pattern) := by
  cases root_form pattern normal with
  | bottom equal =>
      exact False.elim (tagged_not_bottom (tagged_shape shape xs xlen) (subtype_trans below equal.1))
  | scalar base equal =>
      have bad := tag_subtype (tagged_shape shape xs xlen) (tagged_scalar base) (subtype_trans below equal.1)
      cases shape <;> cases bad
  | nominal name args equal =>
      have bad := tag_subtype (tagged_shape shape xs xlen) (tagged_nominal name args) (subtype_trans below equal.1)
      cases shape <;> cases bad
  | structural middle values midcanonical length equal =>
      have same := shape_bracket shape middle canonical midcanonical xlen length zlen
        (subtype_trans below equal.1) (subtype_trans equal.2 above)
      subst middle
      exact ⟨values,length,equal⟩
  | record label payload rest source equal =>
      have tag := tag_subtype (tagged_shape shape xs xlen) (tagged_record label payload rest) (subtype_trans below equal.1)
      cases shape with
      | pair | variant => cases tag
      | exactEmpty =>
          have seen : CommonNominalFullDemand.ProbeAt Common.rowLe 0 ⟨fun _ => .bottom,fun _ => []⟩
              (observeTy 0 (record label payload rest)) (.field label .trivial) := by
                change CommonNominalFullDemand.ProbeAt _ 0 _ (.record label _ _) _
                rw [CommonNominalFullDemand.probeAt_record_field,ite_eq_left rfl]
                exact CommonNominalFullDemand.probeAt_trivial ..
          have bad := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp
            ((subtype_trans below equal.1) 0) 0 _ _ seen
          exact False.elim bad
      | record keys =>
          obtain ⟨name,first,last,rfl⟩ := source
          let pattern := Pattern.record name first last
          let fields := (entries pattern).map fun field => (field.1,eval (algebra constructors interpretation) (fun _ => .bottom) field.2)
          have unique : (fields.map Prod.fst).Nodup := by
            simpa only [fields,List.map_map,Function.comp_def,labels_entries] using fields_unique pattern normal
          have nonempty : fields ≠ [] := by simp [fields,pattern,entries]
          have terminal := terminal_fields (constructors := constructors) (interpretation := interpretation) (variables := fun _ => .bottom) (tail pattern) (tail_closed pattern closed) (tail_normal pattern normal) (tail_not_record pattern)
          rw [record_shape keys xs xlen,eval_fold pattern] at below
          rw [record_shape keys zs zlen,eval_fold pattern] at above
          obtain ⟨values,len,eqv⟩ := GeneralDictionaryRecordBracket216.bracket nonempty unique terminal canonical xlen zlen below above
          refine ⟨values,len,?_⟩
          rw [eval_fold pattern]
          exact eqv
end Yulang.GeneralDictionaryCountedBracket216
