import Yulang.GeneralNominalMatchedAssembly

/-! A finite canonical input bracketed by two observations of one head has
that head. Record signatures are recovered from both directed comparisons. -/
namespace Yulang.GeneralNominalFiniteBracket
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalFiniteHeadInversion
open GeneralNominalStructuralReadback GeneralNominalRecordInversion GeneralNormalizedObservation
open CommonNominalFullCarrier

theorem subtype_head (first last : Test) (xs : Fin (arity first) → Ty) (ys : Fin (arity last) → Ty)
    (below : Subtype (build first xs) (build last ys)) : head first = head last := by
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [head last]⟩
  have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env (.role 0)
    ((build_role last ys env).mpr (List.mem_singleton_self _))
  exact List.mem_singleton.mp ((build_role first xs env).mp accepted)

theorem record_fields_below (first last : List (Nat × Ty))
    (below : Subtype (recordValues first) (recordValues last)) : last.map Prod.fst ⊆ first.map Prod.fst := by
  intro label member
  apply (field_presence first label).mp
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 _ _
    ((field_presence last label).mpr member)

theorem record_signature_bracket (first middle : List Nat) (xs ys zs : List Ty)
    (one : first.Pairwise (· < ·)) (two : middle.Pairwise (· < ·))
    (xlen : xs.length = first.length) (ylen : ys.length = middle.length) (zlen : zs.length = first.length)
    (lower : Subtype (shapeValue (.record first) xs) (shapeValue (.record middle) ys))
    (upper : Subtype (shapeValue (.record middle) ys) (shapeValue (.record first) zs)) : first = middle := by
  rw [record_shape first xs xlen,record_shape middle ys ylen] at lower
  rw [record_shape middle ys ylen,record_shape first zs zlen] at upper
  have down := record_fields_below _ _ lower
  have up := record_fields_below _ _ upper
  simp only [List.map_fst_zip (Nat.le_of_eq xlen.symm),List.map_fst_zip (Nat.le_of_eq ylen.symm),
    List.map_fst_zip (Nat.le_of_eq zlen.symm)] at down up
  have perm := (List.perm_ext_iff_of_nodup (one.imp (fun less => Nat.ne_of_lt less))
    (two.imp (fun less => Nat.ne_of_lt less))).mpr (fun _ => ⟨fun mem => up mem,fun mem => down mem⟩)
  exact List.Perm.eq_of_pairwise (le := Nat.le) (fun _ _ _ _ a b => Nat.le_antisymm a b)
    (one.imp (fun less => Nat.le_of_lt less)) (two.imp (fun less => Nat.le_of_lt less)) perm

theorem record_exact_empty_bracket (first last : List (Nat × Ty))
    (same : first.map Prod.fst = last.map Prod.fst)
    (lower : Subtype (recordValues first) exactEmpty)
    (upper : Subtype exactEmpty (recordValues last)) : False := by
  cases first with
  | nil =>
    have bad := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (lower 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.optional 0 .impossible) (Or.inl (by simp))
    change (CommonNominalFinite.Observation.impossible : CommonNominalFinite.Observation Row) = .trivial at bad
    cases bad
  | cons entry rest =>
    have member : entry.1 ∈ last.map Prod.fst := by rw [← same]; exact List.mem_cons_self ..
    exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (upper 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.field entry.1 .trivial) ((field_presence last entry.1).mpr member)

theorem test_bracket (first middle : Test) (xs : Fin (arity first) → Ty)
    (ys : Fin (arity middle) → Ty) (zs : Fin (arity first) → Ty)
    (one : TestCanonical first) (two : TestCanonical middle)
    (lower : Subtype (build first xs) (build middle ys))
    (upper : Subtype (build middle ys) (build first zs)) : first = middle := by
  have same := subtype_head first middle xs ys lower
  cases first with
  | scalar base =>
    cases middle with
    | scalar other => exact congrArg Test.scalar (CommonNominalFullDemand.Head.base.inj same)
    | nominal => cases same
    | structural shape => cases shape <;> cases same
  | nominal name count =>
    cases middle with
    | scalar => cases same
    | nominal other length =>
      obtain ⟨rfl,rfl⟩ := CommonNominalFullDemand.Head.nominal.inj same
      rfl
    | structural shape => cases shape <;> cases same
  | structural shape =>
    cases middle with
    | scalar => cases shape <;> cases same
    | nominal => cases shape <;> cases same
    | structural other =>
      cases shape <;> cases other <;> try cases same
      all_goals try rfl
      case record.record.refl labels middle =>
        exact congrArg (fun labels => Test.structural (.record labels))
          (record_signature_bracket labels middle _ _ _ one two
            (List.length_ofFn ..) (List.length_ofFn ..) (List.length_ofFn ..) lower upper)
      case record.exactEmpty.refl labels =>
        apply False.elim
        change Subtype (shapeValue (.record labels) (List.ofFn xs)) exactEmpty at lower
        change Subtype exactEmpty (shapeValue (.record labels) (List.ofFn zs)) at upper
        rw [record_shape labels (List.ofFn xs) (by exact List.length_ofFn ..)] at lower
        rw [record_shape labels (List.ofFn zs) (by exact List.length_ofFn ..)] at upper
        exact record_exact_empty_bracket (labels.zip (List.ofFn xs)) (labels.zip (List.ofFn zs))
          (by rw [List.map_fst_zip (by exact Nat.le_of_eq (List.length_ofFn (f := xs)).symm),List.map_fst_zip (by exact Nat.le_of_eq (List.length_ofFn (f := zs)).symm)]) lower upper
      case exactEmpty.record.refl labels =>
        apply False.elim
        change Subtype exactEmpty (shapeValue (.record labels) (List.ofFn ys)) at lower
        change Subtype (shapeValue (.record labels) (List.ofFn ys)) exactEmpty at upper
        rw [record_shape labels (List.ofFn ys) (by exact List.length_ofFn ..)] at lower upper
        exact record_exact_empty_bracket _ _ rfl upper lower

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

private theorem observe_records (depth : Nat) (fields : List (Nat × Ty)) :
    observeTy depth (recordValues fields) = finiteRecord (fields.map fun entry =>
      (entry.1,CommonNominalSyntax.observe (CommonNominalSyntax.graph Row) depth (.node entry.2))) := by
  induction fields with
  | nil => rfl
  | cons head tail ih =>
    change CommonNominalFinite.Ty.record head.1 _ (observeTy depth (recordValues tail)) = _
    rw [ih]
    rfl


theorem record_payload_below (a b : Ty) (first last : List (Nat × Ty)) (uniqueFirst : (first.map Prod.fst).Nodup)
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

theorem shape_payload_below {index : Nat} {a b : Ty} (shape : Shape) (canonical : shape.Canonical)
    (first last : List Ty) (one : first.length = shape.arity) (two : last.length = shape.arity)
    (left : first[index]? = some a) (right : last[index]? = some b)
    (same : Subtype (shapeValue shape first) (shapeValue shape last)) : Subtype a b := by
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
    have forward := (common_pair_iff x y u v).mp same
    cases index with
    | zero => cases Option.some.inj left; cases Option.some.inj right; exact forward.1
    | succ index => cases index with
      | zero => cases Option.some.inj left; cases Option.some.inj right; exact forward.2
      | succ index => cases left
  | variant tag =>
    obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp one
    obtain ⟨y,rfl⟩ := List.length_eq_one_iff.mp two
    cases index with
    | zero => cases Option.some.inj left; cases Option.some.inj right
              exact (common_variant_iff tag _ _).mp same
    | succ index => cases left
  | record labels =>
    rw [record_shape labels first one,record_shape labels last two] at same
    have unique : labels.Nodup := canonical.imp (fun strict => Nat.ne_of_lt strict)
    have bound : index < labels.length := by
      have bound := (List.getElem?_eq_some_iff.mp left).1
      simpa only [one,Shape.arity] using bound
    apply record_payload_below a b (label := labels[index]) (labels.zip first) (labels.zip last)
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


theorem finite_bracket (term : Expr Nat) (closed : term.leaves = []) (canonical : Canonical term)
    (test : Test) (testCanonical : TestCanonical test) (lower upper : Fin (arity test) → Ty)
    (below : Subtype (build test lower) (denote (fun _ => .bottom) term))
    (above : Subtype (denote (fun _ => .bottom) term) (build test upper)) :
    ∃ children, term = .node test children := by
  cases term with
  | leaf => simp [Expr.leaves] at closed
  | node middle children =>
    have same := test_bracket test middle lower (fun index => denote (fun _ => .bottom) (children index)) upper
      testCanonical canonical.1 below above
    subst middle
    exact ⟨children,rfl⟩

theorem structural_children (shape : Shape) (canonical : shape.Canonical)
    (lower middle upper : Fin shape.arity → Ty)
    (below : Subtype (build (.structural shape) lower) (build (.structural shape) middle))
    (above : Subtype (build (.structural shape) middle) (build (.structural shape) upper)) :
    ∀ index, Subtype (lower index) (middle index) ∧ Subtype (middle index) (upper index) := by
  intro index
  constructor
  · exact shape_payload_below (index := index.val) shape canonical (List.ofFn lower) (List.ofFn middle)
      (List.length_ofFn ..) (List.length_ofFn ..) (by simp [index.isLt]) (by simp [index.isLt]) below
  · exact shape_payload_below (index := index.val) shape canonical (List.ofFn middle) (List.ofFn upper)
      (List.length_ofFn ..) (List.length_ofFn ..) (by simp [index.isLt]) (by simp [index.isLt]) above


def reindex {shape expected : Shape} (same : shape = expected) (values : Fin shape.arity → α) : Fin expected.arity → α :=
  fun index => values ⟨index.val,by rw [same]; exact index.isLt⟩

theorem structural_slot (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots) (kind : Fin state.view.kinds)
    (children : Fin (state.view.shapes kind).arity → Fin state.base.slots)
    (recorded : state.view.heads slot = .structural kind children)
    (same : state.view.shapes kind = shape) :
    Equivalent (model (state.base.source slot)).1
      (build (.structural shape) (fun index => (model (state.base.source (reindex same children index))).1)) := by
  have equal := GeneralNominalState.normalized_models state model valid slot
    ((state.view.shapes kind).term children) (by rw [recorded]; rfl)
  have represented := GeneralNominalStructuralReadback.shape_values (state.view.shapes kind) children
    (GeneralNominalCommonBridge.assignment state.base model)
  have result : Equivalent (model (state.base.source slot)).1
      (build (.structural (state.view.shapes kind)) (fun index => (model (state.base.source (children index))).1)) := by
    change Equivalent _ (shapeValue _ _)
    erw [represented]
    exact equal
  cases same
  exact result

theorem structural_interval (state : GeneralNominalState.State) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state model) (bounds : GeneralNominalInspection.Bounds state)
    (lowerKind upperKind : Fin state.view.kinds)
    (lower : Fin (state.view.shapes lowerKind).arity → Fin state.base.slots)
    (upper : Fin (state.view.shapes upperKind).arity → Fin state.base.slots)
    (lowerAt : state.view.heads bounds.1 = .structural lowerKind lower)
    (upperAt : state.view.heads bounds.2 = .structural upperKind upper)
    (lowerShape : state.view.shapes lowerKind = shape) (upperShape : state.view.shapes upperKind = shape)
    (term : Expr Nat) (closed : term.leaves = []) (canonical : Canonical term)
    (contained : Fits state model bounds (denote (fun _ => .bottom) term)) :
    ∃ children : Fin shape.arity → Expr Nat, term = .node (.structural shape) children ∧
      ∀ index, Fits state model (reindex lowerShape lower index,reindex upperShape upper index)
        (denote (fun _ => .bottom) (children index)) := by
  have one := structural_slot state model valid bounds.1 lowerKind lower lowerAt lowerShape
  have two := structural_slot state model valid bounds.2 upperKind upper upperAt upperShape
  have below := subtype_trans one.2 contained.1
  have above := subtype_trans contained.2 two.1
  have shapeCanonical : shape.Canonical := lowerShape ▸ state.view.canonical lowerKind
  obtain ⟨children,equal⟩ := finite_bracket term closed canonical (.structural shape) shapeCanonical _ _ below above
  refine ⟨children,equal,?_⟩
  rw [equal] at below above
  exact structural_children shape shapeCanonical _ _ _ below above

end Yulang.GeneralNominalFiniteBracket
