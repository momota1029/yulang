import Yulang.GeneralNominalCompoundReadback
import Yulang.GeneralNominalStructuralReadback

/-! A finite observational term determines one carrier equivalence class.
This includes structural constructors nested under nominal input requests. -/
namespace Yulang.GeneralNominalReadbackFunctionality
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNormalizedObservation (Shape recordTerm)
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

private theorem record_congr (fields : List (Nat × Fin slots))
    (first last : Fin slots → Ty) (equal : ∀ index, Equivalent (first index) (last index)) :
    Equivalent
      ((recordTerm (fields.map fun field => (field.1,TyTerm.var field.2)) .emptyRecord).eval model
        (fun index => (first index,Common.rowEmpty)))
      ((recordTerm (fields.map fun field => (field.1,TyTerm.var field.2)) .emptyRecord).eval model
        (fun index => (last index,Common.rowEmpty))) := by
  induction fields with
  | nil => exact ⟨subtype_refl _,subtype_refl _⟩
  | cons field rest ih =>
    exact ⟨common_record_mono field.1 (equal field.2).1 ih.1,
      common_record_mono field.1 (equal field.2).2 ih.2⟩

theorem shape_congr (shape : Shape) (first last : List Ty)
    (equal : ∀ index : Fin shape.arity,
      Equivalent ((first[index.val]?).getD .bottom) ((last[index.val]?).getD .bottom)) :
    Equivalent (shapeValue shape first) (shapeValue shape last) := by
  cases shape with
  | pair => exact ⟨(common_pair_iff ..).mpr ⟨(equal ⟨0,by simp [Shape.arity]⟩).1,(equal ⟨1,by simp [Shape.arity]⟩).1⟩,
      (common_pair_iff ..).mpr ⟨(equal ⟨0,by simp [Shape.arity]⟩).2,(equal ⟨1,by simp [Shape.arity]⟩).2⟩⟩
  | variant tag => exact ⟨(common_variant_iff ..).mpr (equal ⟨0,by simp [Shape.arity]⟩).1,
      (common_variant_iff ..).mpr (equal ⟨0,by simp [Shape.arity]⟩).2⟩
  | exactEmpty => exact ⟨subtype_refl _,subtype_refl _⟩
  | record labels =>
    have result := record_congr (List.ofFn fun index : Fin labels.length => (labels[index],index))
      (fun index => (first[index.val]?).getD .bottom)
      (fun index => (last[index.val]?).getD .bottom) equal
    simpa only [List.map_ofFn,shapeValue,Shape.term,Shape.arity,Function.comp_def,CommonNominalFullCarrier.model] using result

variable {model : GeneralNominalCommonBridge.Assignment}

def Unique (model : GeneralNominalCommonBridge.Assignment) (root : Origin) : Prop :=
  ∀ a b, Observes model root a → Observes model root b → Equivalent a b

def TestCanonical : Test → Prop
  | .structural shape => shape.Canonical
  | _ => True

def Canonical : Expr α → Prop
  | .leaf _ => True
  | .node test children => (TestCanonical test) ∧ ∀ index, Canonical (children index)

theorem source_unique (model : GeneralNominalCommonBridge.Assignment) (identity : Nat) :
    Unique model (.source identity) := by
  intro a b one two
  cases one; cases two
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem projection_unique (unique : Unique model root) (test : Test)
    (canonical : TestCanonical test)
    (index : Fin (arity test)) : Unique model (project root test index) := by
  intro a b one two
  cases test with
  | scalar base => exact Fin.elim0 index
  | nominal name count =>
    cases one with
    | nominal parent equal found =>
      cases two with
      | nominal other last located =>
        have same := unique _ _ parent other
        exact ((nominal_regular_invariant_exact ..).mp
          (subtype_trans equal.2 (subtype_trans same.1 last.1))).2.2 _ _ _ found located
  | structural shape =>
    cases one with
    | structural parent length equal found =>
      cases two with
      | structural other lastLength last located =>
        have same := unique _ _ parent other
        exact GeneralNominalStructuralReadback.shape_payload shape canonical _ _ length lastLength found located
          ⟨subtype_trans equal.2 (subtype_trans same.1 last.1),
            subtype_trans last.2 (subtype_trans same.2 equal.1)⟩

theorem nominal_argument (unique : Unique model root)
    (rootValue : Equivalent value (nominal name arguments))
    (rootSeen : Observes model root value) (found : arguments[index]? = some argument)
    (seen : Observes model (.nominal root name index) actual) :
    ArgumentEquivalent argument (.inl actual) := by
  cases seen with
  | nominal parent equal located =>
    have same := unique _ _ rootSeen parent
    exact ((nominal_regular_invariant_exact ..).mp
      (subtype_trans rootValue.2 (subtype_trans same.1 equal.1))).2.2 _ _ _ found located

theorem heads_same (firstUnique : Unique model first) (lastUnique : Unique model last)
    (firstHead : Head model first test) (lastHead : Head model last test)
    (children : ∀ index : Fin (arity test), Same model (project first test index) (project last test index)) :
    Same model first last := by
  refine ⟨firstHead.1,lastHead.1,?_⟩
  intro a b one two
  cases test with
  | scalar base =>
    have left := firstHead.2 a one
    have right := lastHead.2 b two
    exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩
  | structural shape =>
    obtain ⟨xs,xlen,xeq⟩ := firstHead.2 a one
    obtain ⟨ys,ylen,yeq⟩ := lastHead.2 b two
    have same := shape_congr shape xs ys (by
      intro index
      have xi : index.val < xs.length := by rw [xlen]; exact index.isLt
      have yi : index.val < ys.length := by rw [ylen]; exact index.isLt
      simp only [List.getElem?_eq_getElem xi,List.getElem?_eq_getElem yi,Option.getD_some]
      exact (children index).2.2 _ _
        (.structural one xlen xeq (List.getElem?_eq_getElem xi))
        (.structural two ylen yeq (List.getElem?_eq_getElem yi)))
    exact ⟨subtype_trans xeq.1 (subtype_trans same.1 yeq.2),
      subtype_trans yeq.1 (subtype_trans same.2 xeq.2)⟩
  | nominal name count =>
    obtain ⟨xs,xlen,xeq⟩ := firstHead.2 a one
    obtain ⟨ys,ylen,yeq⟩ := lastHead.2 b two
    have arguments : ArgumentsEquivalent xs ys := by
      intro index x y xf yf
      have bounded : index < count := by
        rw [← xlen]; exact (List.getElem?_eq_some_iff.mp xf).1
      obtain ⟨u,us⟩ := (children ⟨index,bounded⟩).1
      obtain ⟨v,vs⟩ := (children ⟨index,bounded⟩).2.1
      have left : ArgumentEquivalent x (.inl u) := nominal_argument firstUnique xeq one xf us
      have right : ArgumentEquivalent y (.inl v) := nominal_argument lastUnique yeq two yf vs
      have middle := (children ⟨index,bounded⟩).2.2 u v us vs
      cases x <;> cases y <;> simp only [ArgumentEquivalent] at *
      · exact ⟨subtype_trans left.1 (subtype_trans middle.1 right.2),
          subtype_trans right.1 (subtype_trans middle.2 left.2)⟩
      all_goals contradiction
    have forward := (nominal_regular_invariant_exact name name xs ys).mpr ⟨rfl,xlen.trans ylen.symm,arguments⟩
    have reverse := (nominal_regular_invariant_exact name name ys xs).mpr ⟨rfl,ylen.trans xlen.symm,?_⟩
    · exact ⟨subtype_trans xeq.1 (subtype_trans forward yeq.2),
        subtype_trans yeq.1 (subtype_trans reverse xeq.2)⟩
    · intro index y x yf xf
      have same := arguments index x y xf yf
      cases x <;> cases y <;> simp only [ArgumentEquivalent] at *
      · exact ⟨same.2,same.1⟩
      · exact same.symm

theorem holds_same (term : Expr Origin) (canonical : Canonical term)
    (firstUnique : Unique model first) (lastUnique : Unique model last)
    (firstReadback : Holds model term first) (lastReadback : Holds model term last) :
    Same model first last := by
  induction term generalizing first last with
  | leaf source => exact same_trans firstReadback (same_symm lastReadback)
  | node test children ih =>
    exact heads_same firstUnique lastUnique firstReadback.1 lastReadback.1
      (fun index => ih index (canonical.2 index)
        (projection_unique firstUnique test canonical.1 index)
        (projection_unique lastUnique test canonical.1 index)
        (firstReadback.2 index) (lastReadback.2 index))

theorem source_readbacks_equal (term : Expr Origin) (canonical : Canonical term)
    (one : Holds model term (.source first)) (two : Holds model term (.source last)) :
    Equivalent (model first).1 (model last).1 :=
  (holds_same term canonical (source_unique model first) (source_unique model last) one two).2.2
    _ _ (.source first) (.source last)

end Yulang.GeneralNominalReadbackFunctionality
