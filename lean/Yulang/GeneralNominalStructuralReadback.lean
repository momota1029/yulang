import Yulang.GeneralNominalActualInspectionSteps

/-! Canonical structural positions have a unique actual payload, including
records with arbitrary nominal or regular payloads. Duplicate field labels
are excluded by the existing normalized-shape certificate. -/
namespace Yulang.GeneralNominalStructuralReadback
open GeneralNominalRecursiveInspection GeneralNormalizedObservation
open CommonNominalFullCarrier

private def finiteRecord (fields : List (Nat × CommonNominalFullDemand.Ty Row)) : CommonNominalFullDemand.Ty Row :=
  fields.foldr (fun entry tail => .record entry.1 entry.2 tail) .emptyRecord

private theorem finite_field (fields : List (Nat × CommonNominalFullDemand.Ty Row))
    (unique : (fields.map Prod.fst).Nodup) (member : (label,payload) ∈ fields)
    (rank : Nat) (env : CommonNominalFullDemand.Environment Row) (obs : CommonNominalFullDemand.Observation Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe rank env (finiteRecord fields) (.field label obs) ↔
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env payload obs := by
  induction fields with
  | nil => cases member
  | cons head tail ih =>
    have nodup := List.nodup_cons.mp unique
    rcases List.mem_cons.mp member with same | later
    · cases same
      simp [finiteRecord,CommonNominalFullDemand.probeAt_record_field]
    · have different : label ≠ head.1 := by
        intro equal
        apply nodup.1
        exact equal ▸ List.mem_map.mpr ⟨(label,payload),later,rfl⟩
      simpa only [finiteRecord,List.foldr_cons,CommonNominalFullDemand.probeAt_record_field,
        different,ite_false] using ih nodup.2 later

def recordValues (fields : List (Nat × Ty)) : Ty := fields.foldr (fun entry tail => record entry.1 entry.2 tail) emptyRecord

private theorem observe_records (depth : Nat) (fields : List (Nat × Ty)) :
    observeTy depth (recordValues fields) = finiteRecord (fields.map fun entry =>
      (entry.1,CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node entry.2))) := by
  induction fields with
  | nil => rfl
  | cons head tail ih =>
    change CommonNominalFinite.Ty.record head.1 _ (observeTy depth (recordValues tail)) = _
    rw [ih]
    rfl

theorem record_payload (first last : List (Nat × Ty))
    (uniqueFirst : (first.map Prod.fst).Nodup) (uniqueLast : (last.map Prod.fst).Nodup)
    (one : (label,a) ∈ first) (two : (label,b) ∈ last)
    (same : Equivalent (recordValues first) (recordValues last)) : Equivalent a b := by
  have project (a b : Ty) (first last : List (Nat × Ty)) (uniqueFirst : (first.map Prod.fst).Nodup)
      (uniqueLast : (last.map Prod.fst).Nodup) (one : (label,a) ∈ first) (two : (label,b) ∈ last)
      (below : Subtype (recordValues first) (recordValues last)) : Subtype a b := by
    intro depth
    have comparison := below (depth+1)
    rw [observe_records,observe_records] at comparison
    apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
    intro rank env obs accepted
    have left := finite_field (first.map (fun entry => (entry.1,CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (depth+1) (.node entry.2)))) (by simpa only [List.map_map,Function.comp_def] using uniqueFirst)
      (List.mem_map.mpr ⟨(label,a),one,rfl⟩) rank env obs
    have right := finite_field (last.map (fun entry => (entry.1,CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) (depth+1) (.node entry.2)))) (by simpa only [List.map_map,Function.comp_def] using uniqueLast)
      (List.mem_map.mpr ⟨(label,b),two,rfl⟩) rank env obs
    exact left.mp ((CommonNominalFullDemand.producerLe_iff_probe _ _).mp comparison rank env (.field label obs)
      (right.mpr accepted))
  exact ⟨project a b first last uniqueFirst uniqueLast one two same.1,
    project b a last first uniqueLast uniqueFirst two one same.2⟩

private theorem record_shape (labels : List Nat) (values : List Ty) (length : values.length = labels.length) :
    shapeValue (.record labels) values = recordValues (labels.zip values) := by
  simp only [shapeValue,Shape.term,recordTerm]
  have evalFold (fields : List (Nat × Core.PresenceGeneration.TyTerm (Fin labels.length))) :
      (fields.foldr (fun field (rest : Core.PresenceGeneration.TyTerm (Fin labels.length)) => .record field.1 field.2 rest) .emptyRecord).eval model
        (fun index => ((values[index.val]?).getD .bottom,Common.rowEmpty)) =
      recordValues (fields.map fun field => (field.1,field.2.eval model
        (fun index => ((values[index.val]?).getD .bottom,Common.rowEmpty)))) := by
    induction fields with
    | nil => rfl
    | cons head tail ih => simp only [List.foldr_cons,Core.PresenceGeneration.TyTerm.eval,List.map_cons,recordValues]; rw [ih]; rfl
  erw [evalFold]
  congr 1
  erw [List.map_ofFn]
  apply List.ext_getElem
  · simp [length]
  · intro index one two
    simp only [List.getElem_ofFn,List.getElem_zip]
    have valueBound : index < values.length := by simpa only [List.length_zip,length,Nat.min_self] using two
    have labelBound : index < labels.length := by simpa only [List.length_ofFn] using one
    change (labels[index]'labelBound,(values[index]?).getD (.bottom : Ty)) = (labels[index]'labelBound,values[index]'valueBound)
    rw [List.getElem?_eq_getElem valueBound]
    rfl

theorem shape_payload {index : Nat} {a b : Ty} (shape : Shape) (canonical : shape.Canonical)
    (first last : List Ty) (one : first.length = shape.arity) (two : last.length = shape.arity)
    (left : first[index]? = some a) (right : last[index]? = some b)
    (same : Equivalent (shapeValue shape first) (shapeValue shape last)) : Equivalent a b := by
  cases shape with
  | exactEmpty =>
    have bound := List.getElem?_eq_some_iff.mp left |>.1
    simp only [Shape.arity] at one
    omega
  | pair =>
    have firstForm : ∃ x y, first = [x,y] := by
      cases first with
      | nil => simp [Shape.arity] at one
      | cons x xs => cases xs with
        | nil => simp [Shape.arity] at one
        | cons y ys => exact ⟨x,y,by have empty : ys = [] := List.eq_nil_of_length_eq_zero (by simp only [Shape.arity,List.length_cons] at one; omega); subst ys; rfl⟩
    have lastForm : ∃ x y, last = [x,y] := by
      cases last with
      | nil => simp [Shape.arity] at two
      | cons x xs => cases xs with
        | nil => simp [Shape.arity] at two
        | cons y ys => exact ⟨x,y,by have empty : ys = [] := List.eq_nil_of_length_eq_zero (by simp only [Shape.arity,List.length_cons] at two; omega); subst ys; rfl⟩
    obtain ⟨x,y,rfl⟩ := firstForm
    obtain ⟨u,v,rfl⟩ := lastForm
    have forward := (common_pair_iff x y u v).mp same.1
    have backward := (common_pair_iff u v x y).mp same.2
    cases index with
    | zero => cases Option.some.inj left; cases Option.some.inj right; exact ⟨forward.1,backward.1⟩
    | succ index => cases index with
      | zero => cases Option.some.inj left; cases Option.some.inj right; exact ⟨forward.2,backward.2⟩
      | succ index => cases left
  | variant tag =>
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp one
    obtain ⟨y,rfl⟩ := List.length_eq_one_iff.mp two
    cases index with
    | zero => cases Option.some.inj left; cases Option.some.inj right
              exact ⟨(common_variant_iff tag _ _).mp same.1,(common_variant_iff tag _ _).mp same.2⟩
    | succ index => cases left
  | record labels =>
    rw [record_shape labels first one,record_shape labels last two] at same
    have unique : labels.Nodup := canonical.imp (fun strict => Nat.ne_of_lt strict)
    have bound : index < labels.length := by
      have bound := (List.getElem?_eq_some_iff.mp left).1
      simpa only [one,Shape.arity] using bound
    apply record_payload (label := labels[index]) (labels.zip first) (labels.zip last)
      (by rw [List.map_fst_zip (by simpa only [Shape.arity] using Nat.le_of_eq one.symm)]; exact unique)
      (by rw [List.map_fst_zip (by simpa only [Shape.arity] using Nat.le_of_eq two.symm)]; exact unique) _ _ same
    · obtain ⟨firstBound,firstAt⟩ := List.getElem?_eq_some_iff.mp left
      have present := List.getElem_mem (l := labels.zip first) (n := index)
        (by simp only [List.length_zip,Nat.lt_min]; exact ⟨bound,firstBound⟩)
      simpa only [List.getElem_zip,firstAt] using present
    · obtain ⟨lastBound,lastAt⟩ := List.getElem?_eq_some_iff.mp right
      have present := List.getElem_mem (l := labels.zip last) (n := index)
        (by simp only [List.length_zip,Nat.lt_min]; exact ⟨bound,lastBound⟩)
      simpa only [List.getElem_zip,lastAt] using present


private theorem record_eval (fields : List (Nat × Core.PresenceGeneration.TyTerm (Fin slots)))
    (assignment : Fin slots → Core.PresenceGeneration.Comp model) :
    (recordTerm fields .emptyRecord).eval model assignment =
      recordValues (fields.map fun field => (field.1,field.2.eval model assignment)) := by
  induction fields with
  | nil => rfl
  | cons head tail ih =>
    change record head.1 (head.2.eval model assignment) ((recordTerm tail .emptyRecord).eval model assignment) = _
    rw [ih]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem shape_values (shape : Shape) (children : Fin shape.arity → Fin slots)
    (assignment : Fin slots → Core.PresenceGeneration.Comp model) :
    shapeValue shape (List.ofFn fun index => (assignment (children index)).1) =
      (shape.term children).eval model assignment := by
  cases shape with
  | pair | variant | exactEmpty =>
    simp [shapeValue,Shape.term,Core.PresenceGeneration.TyTerm.eval,Shape.arity]
    <;> rfl
  | record labels =>
    erw [record_shape labels _ (List.length_ofFn ..)]
    change _ = (recordTerm _ .emptyRecord).eval model assignment
    rw [record_eval]
    congr 1
    rw [List.map_ofFn]
    apply List.ext_getElem
    · simp
    · intro index one two
      simp [List.getElem_zip,List.getElem_ofFn,Function.comp_def,Core.PresenceGeneration.TyTerm.eval]

set_option backward.isDefEq.respectTransparency false in
theorem actual_structural_readback (state : GeneralNominalSaturationState.State roles)
    (parent : Fin state.context.state.base.slots) (kind : Fin state.context.state.view.kinds)
    (children : Fin (state.context.state.view.shapes kind).arity → Fin state.context.state.base.slots)
    (recorded : state.context.state.view.heads parent = .structural kind children)
    (index : Fin (state.context.state.view.shapes kind).arity) :
    GeneralNominalActualInspectionSteps.Represents state
      (.structural (.source (state.context.state.base.source parent)) (state.context.state.view.shapes kind) index.val)
      (state.context.state.base.source (children index)) := by
  intro model valid
  let values := List.ofFn fun position => (model (state.context.state.base.source (children position))).1
  have length : values.length = (state.context.state.view.shapes kind).arity := List.length_ofFn ..
  have found : values[index.val]? = some (model (state.context.state.base.source (children index))).1 := by
    simp only [values,List.getElem?_ofFn]
    split
    · rfl
    · exact False.elim (by omega)
  have equal := GeneralNominalState.normalized_models state.context.state model valid.1 parent
    ((state.context.state.view.shapes kind).term children) (by rw [recorded]; rfl)
  have equal : Equivalent (model (state.context.state.base.source parent)).1
      (shapeValue (state.context.state.view.shapes kind) values) := by
    rw [show values = List.ofFn (fun index =>
      ((GeneralNominalCommonBridge.assignment state.context.state.base model) (children index)).1) from rfl]
    erw [shape_values]
    exact equal
  have seen : Observes model (.structural (.source (state.context.state.base.source parent))
      (state.context.state.view.shapes kind) index.val) (model (state.context.state.base.source (children index))).1 :=
    .structural (.source _) length equal found
  refine ⟨⟨_,seen⟩,⟨_,.source _⟩,?_⟩
  intro a b observed source
  cases source
  cases observed with
  | structural parentSeen alternateLength alternateEqual alternateAt =>
    cases parentSeen
    exact shape_payload _ (state.context.state.view.canonical kind) _ values alternateLength length alternateAt found
      ⟨subtype_trans alternateEqual.2 equal.1,subtype_trans equal.2 alternateEqual.1⟩

end Yulang.GeneralNominalStructuralReadback
