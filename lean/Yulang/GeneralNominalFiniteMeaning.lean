import Yulang.GeneralNominalReadbackFunctionality

/-! Finite constructor meanings and directional materialization. Structural
constructors preserve containment; nominal parameters use exact values. -/
namespace Yulang.GeneralNominalFiniteMeaning
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms GeneralNominalMaterialization
open GeneralNominalReadbackFunctionality
open GeneralNormalizedObservation (Shape recordTerm)
open CommonNominalFullCarrier
open Core.PresenceGeneration (TyTerm)

def build (test : Test) (children : Fin (arity test) → Ty) : Ty :=
  match test with
  | .scalar base => .base base
  | .structural shape => shapeValue shape (List.ofFn children)
  | .nominal name _ => nominal name (List.ofFn fun index => .inl (children index))

def denote (values : α → Ty) : Expr α → Ty
  | .leaf name => values name
  | .node test children => build test (fun index => denote values (children index))

def childMode : Test → Mode → Mode
  | .nominal _ _,_ => .actual
  | _,mode => mode

def Approx : Mode → Ty → Ty → Prop
  | .lower,first,last => Subtype first last
  | .upper,first,last => Subtype last first
  | .actual,first,last => Equivalent first last

def At (model : GeneralNominalCommonBridge.Assignment) (mode : Mode) (root : Origin) (value : Ty) : Prop :=
  (∃ actual, Observes model root actual) ∧
    ∀ actual, Observes model root actual → Approx mode actual value

theorem equivalent_approx (equal : Equivalent first last) (mode : Mode) : Approx mode first last := by
  cases mode
  · exact equal.1
  · exact equal.2
  · exact equal

theorem approx_left (equal : Equivalent first middle) (below : Approx mode middle last) :
    Approx mode first last := by
  cases mode with
  | lower => exact subtype_trans equal.1 below
  | upper => exact subtype_trans below equal.2
  | actual => exact ⟨subtype_trans equal.1 below.1,subtype_trans below.2 equal.2⟩

private theorem record_mono (fields : List (Nat × Fin slots))
    (first last : Fin slots → Ty) (below : ∀ index, Subtype (first index) (last index)) :
    Subtype
      ((recordTerm (fields.map fun field => (field.1,TyTerm.var field.2)) .emptyRecord).eval model
        (fun index => (first index,Common.rowEmpty)))
      ((recordTerm (fields.map fun field => (field.1,TyTerm.var field.2)) .emptyRecord).eval model
        (fun index => (last index,Common.rowEmpty))) := by
  induction fields with
  | nil => exact subtype_refl _
  | cons field rest ih => exact common_record_mono field.1 (below field.2) ih

theorem shape_mono (shape : Shape) (first last : List Ty)
    (below : ∀ index : Fin shape.arity,
      Subtype ((first[index.val]?).getD .bottom) ((last[index.val]?).getD .bottom)) :
    Subtype (shapeValue shape first) (shapeValue shape last) := by
  cases shape with
  | pair =>
    exact (common_pair_iff ..).mpr
      ⟨below ⟨0,by simp [Shape.arity]⟩,below ⟨1,by simp [Shape.arity]⟩⟩
  | variant tag => exact (common_variant_iff ..).mpr (below ⟨0,by simp [Shape.arity]⟩)
  | exactEmpty => exact subtype_refl _
  | record labels =>
    have result := record_mono (List.ofFn fun index : Fin labels.length => (labels[index],index))
      (fun index => (first[index.val]?).getD .bottom)
      (fun index => (last[index.val]?).getD .bottom) below
    simpa only [List.map_ofFn,shapeValue,Shape.term,Shape.arity,Function.comp_def,CommonNominalFullCarrier.model] using result

theorem shape_approx (shape : Shape) (first last : List Ty)
    (below : ∀ index : Fin shape.arity,
      Approx mode ((first[index.val]?).getD .bottom) ((last[index.val]?).getD .bottom)) :
    Approx mode (shapeValue shape first) (shapeValue shape last) := by
  cases mode with
  | lower => exact shape_mono shape first last below
  | upper => exact shape_mono shape last first below
  | actual => exact ⟨shape_mono shape first last (fun index => (below index).1),
      shape_mono shape last first (fun index => (below index).2)⟩

variable {model : GeneralNominalCommonBridge.Assignment}

theorem assemble (test : Test) (mode : Mode) (values : Fin (arity test) → Ty)
    (unique : Unique model root) (head : Head model root test)
    (children : ∀ index, At model (childMode test mode) (project root test index) (values index)) :
    At model mode root (build test values) := by
  refine ⟨head.1,?_⟩
  intro actual seen
  cases test with
  | scalar base => exact equivalent_approx (head.2 actual seen) mode
  | structural shape =>
    obtain ⟨xs,length,equal⟩ := head.2 actual seen
    apply approx_left equal
    apply shape_approx shape xs (List.ofFn values)
    intro index
    have bounded : index.val < xs.length := by rw [length]; exact index.isLt
    have child := (children index).2 _
      (.structural seen length equal (List.getElem?_eq_getElem bounded))
    have atValue : (List.ofFn values)[index.val]? = some (values index) := by
      rw [List.getElem?_ofFn]
      split
      · rfl
      · rename_i absent
        exact False.elim (absent index.isLt)
    rw [List.getElem?_eq_getElem bounded,atValue]
    exact child
  | nominal name count =>
    obtain ⟨xs,length,equal⟩ := head.2 actual seen
    have args : ArgumentsEquivalent xs (List.ofFn fun index => (Sum.inl (values index) : Argument)) := by
      intro position first last found located
      have bounded : position < count := by
        rw [← length]; exact (List.getElem?_eq_some_iff.mp found).1
      let index : Fin (arity (.nominal name count)) := ⟨position,bounded⟩
      have lastEq : last = .inl (values index) := by
        have same : (List.ofFn fun index => (Sum.inl (values index) : Argument))[position]? = some (.inl (values index)) := by
          simp [index,bounded,arity]
        exact Option.some.inj (located.symm.trans same)
      subst last
      obtain ⟨child,childSeen⟩ := (children index).1
      have same := nominal_argument unique equal seen found childSeen
      have exactChild := (children index).2 child childSeen
      cases first with
      | inr row => exact False.elim same
      | inl value => exact ⟨subtype_trans same.1 exactChild.1,subtype_trans exactChild.2 same.2⟩
    have forward := (nominal_regular_invariant_exact name name xs _).mpr
      ⟨rfl,by simpa only [List.length_ofFn,arity] using length,args⟩
    have reverse := (nominal_regular_invariant_exact name name (List.ofFn fun index => (Sum.inl (values index) : Argument)) xs).mpr
      ⟨rfl,by simpa only [List.length_ofFn,arity] using length.symm,?_⟩
    · exact equivalent_approx
        ⟨subtype_trans equal.1 forward,subtype_trans reverse equal.2⟩ mode
    · intro position first last found located
      have same := args position last first located found
      cases first <;> cases last <;> simp only [ArgumentEquivalent] at *
      · exact ⟨same.2,same.1⟩
      · exact same.symm

theorem denote_bind (term : Expr α) (substitution : α → Expr β) (values : β → Ty) :
    denote values (term.bind substitution) = denote (fun name => denote values (substitution name)) term := by
  induction term with
  | leaf name => rfl
  | node test children ih =>
    simp only [Expr.bind,denote]
    congr 1
    funext index
    exact ih index

theorem denote_agree (term : Expr α) (first last : α → Ty)
    (agree : ∀ name ∈ term.leaves, first name = last name) : denote first term = denote last term := by
  induction term with
  | leaf name => exact agree name (List.mem_singleton_self _)
  | node test children ih =>
    simp only [denote]
    congr 1
    funext index
    apply ih index
    intro name member
    apply agree name
    simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
    exact ⟨_,⟨index,rfl⟩,member⟩

theorem closed_independent (term : Expr α) (closed : term.leaves = []) (first last : α → Ty) :
    denote first term = denote last term :=
  denote_agree term first last (by intro name member; rw [closed] at member; cases member)

theorem at_unique (meaning : At model .actual root value) : Unique model root := by
  intro first last one two
  exact ⟨subtype_trans (meaning.2 first one).1 (meaning.2 last two).2,
    subtype_trans (meaning.2 last two).1 (meaning.2 first one).2⟩

theorem project_value (test : Test) (canonical : TestCanonical test)
    (values : Fin (arity test) → Ty) (meaning : At model .actual root (build test values))
    (index : Fin (arity test)) : At model .actual (project root test index) (values index) := by
  obtain ⟨parent,observed⟩ := meaning.1
  have equal := meaning.2 parent observed
  have found : Observes model (project root test index) (values index) := by
    cases test with
    | scalar base => exact Fin.elim0 index
    | structural shape =>
      have located : (List.ofFn values)[index.val]? = some (values index) := by
        rw [List.getElem?_ofFn]
        split
        · rfl
        · rename_i absent; exact False.elim (absent index.isLt)
      exact .structural observed List.length_ofFn equal located
    | nominal name count =>
      exact .nominal observed equal (by simp [index.isLt])
  refine ⟨⟨_,found⟩,?_⟩
  intro actual seen
  exact projection_unique (at_unique meaning) test canonical index actual _ seen found

/-- A finite path follows explicit constructor positions, with no nominal
body edge. Its endpoint is an actual subterm of the finite readback. -/
inductive Follows : Origin → Expr α → Origin → Expr α → Prop
  | root : Follows root term root term
  | child (test : Test) (children : Fin (arity test) → Expr α) (index : Fin (arity test)) :
      Follows root term parent (.node test children) →
      Follows root term (project parent test index) (children index)

theorem followed_readback (path : Follows root (term : Expr α) endpoint part)
    (canonical : Canonical term) (values : α → Ty) (meaning : At model .actual root (denote values term)) :
    Canonical part ∧ At model .actual endpoint (denote values part) := by
  induction path with
  | root => exact ⟨canonical,meaning⟩
  | child test children index prior ih =>
    exact ⟨ih.1.2 index,project_value test ih.1.1 _ ih.2 index⟩

theorem followed_leaves (path : Follows root term endpoint part) : part.leaves ⊆ term.leaves := by
  induction path with
  | root => exact fun _ member => member
  | child test children index prior ih =>
    intro name member
    apply ih
    simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
    exact ⟨_,⟨index,rfl⟩,member⟩

theorem followed_closed (path : Follows root term endpoint part) (closed : term.leaves = []) : part.leaves = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name member
  have present := followed_leaves path member
  rw [closed] at present
  cases present

end Yulang.GeneralNominalFiniteMeaning
