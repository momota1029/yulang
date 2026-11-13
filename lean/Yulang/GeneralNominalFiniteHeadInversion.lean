import Yulang.GeneralNominalSourceProjection

/-! Finite constructor heads are determined by their full carrier meaning.
Record signatures use canonical order, and exact-empty is kept distinct from
an empty record. No inverse of the constructor catalogue is required. -/
namespace Yulang.GeneralNominalFiniteHeadInversion
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalRecordInversion
open GeneralNominalStructuralReadback GeneralNormalizedObservation
open CommonNominalFullCarrier

def head : Test → CommonNominalFullDemand.Head
  | .scalar base => .base base
  | .nominal name count => .nominal name count
  | .structural .pair => .pair
  | .structural (.variant tag) => .variant tag
  | .structural (.record _) | .structural .exactEmpty => .records

theorem record_role (fields : List (Nat × Ty)) (env : CommonNominalFullDemand.Environment Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe 0 env
      (observeTy 0 (recordValues fields)) (.role 0) ↔ .records ∈ env.roles 0 := by
  cases fields <;> rfl

theorem build_role (test : Test) (values : Fin (arity test) → Ty)
    (env : CommonNominalFullDemand.Environment Row) :
    CommonNominalFullDemand.ProbeAt Common.rowLe 0 env
      (observeTy 0 (build test values)) (.role 0) ↔ head test ∈ env.roles 0 := by
  cases test with
  | scalar base => rfl
  | nominal name count =>
    simp only [build,observe_nominal]
    change CommonNominalFullDemand.Head.nominal name
      ((List.ofFn (fun index => (Sum.inl (values index) : Argument))).map (argumentAt 0)).length ∈ env.roles 0 ↔ _
    simp only [List.length_map,List.length_ofFn,arity,head]
  | structural shape =>
    cases shape with
    | pair | variant | exactEmpty => rfl
    | record labels =>
      change CommonNominalFullDemand.ProbeAt _ _ _ (observeTy 0 (shapeValue (.record labels) _)) _ ↔ _
      rw [record_shape labels (List.ofFn values) (by exact List.length_ofFn ..)]
      exact record_role _ env

theorem equivalent_head (first last : Test) (xs : Fin (arity first) → Ty)
    (ys : Fin (arity last) → Ty) (equal : Equivalent (build first xs) (build last ys)) :
    head first = head last := by
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [head last]⟩
  have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0 env (.role 0)
    ((build_role last ys env).mpr (List.mem_singleton_self _))
  exact List.mem_singleton.mp ((build_role first xs env).mp accepted)

theorem record_not_exactEmpty (fields : List (Nat × Ty)) :
    ¬ Equivalent (recordValues fields) exactEmpty := by
  intro equal
  cases fields with
  | nil =>
    have bad := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.optional 0 .impossible) (Or.inl (by simp))
    change (CommonNominalFinite.Observation.impossible : CommonNominalFinite.Observation Row) = .trivial at bad
    cases bad
  | cons entry rest =>
    have accepted := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.2 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.field entry.1 .trivial)
      ((field_presence (entry::rest) entry.1).mpr (by simp))
    exact accepted

theorem test_equal (first last : Test) (xs : Fin (arity first) → Ty)
    (ys : Fin (arity last) → Ty) (one : TestCanonical first) (two : TestCanonical last)
    (equal : Equivalent (build first xs) (build last ys)) : first = last := by
  have same := equivalent_head first last xs ys equal
  cases first with
  | scalar base =>
    cases last with
    | scalar other => exact congrArg Test.scalar (CommonNominalFullDemand.Head.base.inj same)
    | nominal => cases same
    | structural shape => cases shape <;> cases same
  | nominal name count =>
    cases last with
    | scalar => cases same
    | nominal other length =>
      obtain ⟨rfl,rfl⟩ := CommonNominalFullDemand.Head.nominal.inj same
      rfl
    | structural shape => cases shape <;> cases same
  | structural shape =>
    cases last with
    | scalar => cases shape <;> cases same
    | nominal => cases shape <;> cases same
    | structural other =>
      cases shape <;> cases other <;> try cases same
      all_goals try rfl
      case record.record.refl labels other =>
        exact congrArg (fun labels => Test.structural (.record labels))
          (record_signatures labels other _ _ one two (List.length_ofFn ..) (List.length_ofFn ..) equal)
      case record.exactEmpty.refl labels =>
        apply False.elim
        apply record_not_exactEmpty (labels.zip (List.ofFn xs))
        change Equivalent (shapeValue (.record labels) (List.ofFn xs)) exactEmpty at equal
        rw [record_shape labels (List.ofFn xs) (by exact List.length_ofFn ..)] at equal
        exact equal
      case exactEmpty.record.refl labels =>
        apply False.elim
        apply record_not_exactEmpty (labels.zip (List.ofFn ys))
        change Equivalent exactEmpty (shapeValue (.record labels) (List.ofFn ys)) at equal
        rw [record_shape labels (List.ofFn ys) (by exact List.length_ofFn ..)] at equal
        exact ⟨equal.2,equal.1⟩

end Yulang.GeneralNominalFiniteHeadInversion
