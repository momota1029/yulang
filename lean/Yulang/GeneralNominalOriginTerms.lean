import Yulang.GeneralNominalSettledSupport

/-! Finite constructor terms with shared observational leaves. A leaf is a
source/projection relation, never a selected interior of an interval. -/
namespace Yulang.GeneralNominalOriginTerms
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def arity : Test → Nat
  | .scalar _ => 0
  | .structural shape => shape.arity
  | .nominal _ count => count

def project (root : Origin) (test : Test) (index : Fin (arity test)) : Origin :=
  match test with
  | .scalar _ => Fin.elim0 index
  | .structural shape => .structural root shape index.val
  | .nominal name _ => .nominal root name index.val

inductive Expr (α : Type) where
  | leaf (name : α)
  | node (test : Test) (children : Fin (arity test) → Expr α)

def Expr.bind (substitution : α → Expr β) : Expr α → Expr β
  | .leaf name => substitution name
  | .node test children => .node test (fun index => (children index).bind substitution)

def Expr.leaves : Expr α → List α
  | .leaf name => [name]
  | .node _ children => (List.ofFn (fun index => (children index).leaves)).flatten

def Same (model : Assignment) (first last : Origin) : Prop :=
  (∃ value, Observes model first value) ∧ (∃ value, Observes model last value) ∧
    ∀ a b, Observes model first a → Observes model last b → Equivalent a b

def Head (model : Assignment) (root : Origin) (test : Test) : Prop :=
  (∃ value, Observes model root value) ∧ ∀ value, Observes model root value → test.Holds value

def Holds (model : Assignment) : Expr Origin → Origin → Prop
  | .leaf source,root => Same model root source
  | .node test children,root => Head model root test ∧
      ∀ index, Holds model (children index) (project root test index)

variable {model : Assignment}

theorem same_trans (first : Same model a b) (last : Same model b c) : Same model a c := by
  obtain ⟨middle,seen⟩ := first.2.1
  refine ⟨first.1,last.2.1,?_⟩
  intro x y one two
  exact ⟨subtype_trans (first.2.2 x middle one seen).1 (last.2.2 middle y seen two).1,
    subtype_trans (last.2.2 middle y seen two).2 (first.2.2 x middle one seen).2⟩

theorem same_symm (same : Same model a b) : Same model b a :=
  ⟨same.2.1,same.1,fun x y one two => ⟨(same.2.2 y x two one).2,(same.2.2 y x two one).1⟩⟩

theorem source_self (model : Assignment) (source : Nat) : Same model (.source source) (.source source) :=
  ⟨⟨_,.source _⟩,⟨_,.source _⟩,by intro a b one two; cases one; cases two; exact ⟨subtype_refl _,subtype_refl _⟩⟩

private theorem equivalent_trans (first : Equivalent a b) (last : Equivalent b c) : Equivalent a c :=
  ⟨subtype_trans first.1 last.1,subtype_trans last.2 first.2⟩

private theorem test_transport (test : Test) (same : Equivalent a b) (valid : test.Holds a) : test.Holds b := by
  cases test with
  | scalar base => exact equivalent_trans ⟨same.2,same.1⟩ valid
  | structural shape =>
      obtain ⟨values,length,equal⟩ := valid
      exact ⟨values,length,equivalent_trans ⟨same.2,same.1⟩ equal⟩
  | nominal name count =>
      obtain ⟨values,length,equal⟩ := valid
      exact ⟨values,length,equivalent_trans ⟨same.2,same.1⟩ equal⟩

private theorem project_seen (same : Same model first last) (test : Test) (index : Fin (arity test))
    (seen : Observes model (project first test index) value) : Observes model (project last test index) value := by
  obtain ⟨other,observed⟩ := same.2.1
  cases test with
  | scalar base => exact Fin.elim0 index
  | structural shape =>
      cases seen with
      | structural parent length equal found =>
          exact .structural observed length
            (equivalent_trans ⟨(same.2.2 _ _ parent observed).2,(same.2.2 _ _ parent observed).1⟩ equal) found
  | nominal name count =>
      cases seen with
      | nominal parent equal found =>
          exact .nominal observed
            (equivalent_trans ⟨(same.2.2 _ _ parent observed).2,(same.2.2 _ _ parent observed).1⟩ equal) found

private theorem project_same_observations
    (same : ∀ value, Observes model first value ↔ Observes model last value)
    (test : Test) (index : Fin (arity test)) (value) :
    Observes model (project first test index) value ↔ Observes model (project last test index) value := by
  cases test with
  | scalar base => exact Fin.elim0 index
  | structural shape =>
      constructor
      · intro seen; cases seen with
        | structural parent length equal found => exact .structural ((same _).mp parent) length equal found
      · intro seen; cases seen with
        | structural parent length equal found => exact .structural ((same _).mpr parent) length equal found
  | nominal name count =>
      constructor
      · intro seen; cases seen with
        | nominal parent equal found => exact .nominal ((same _).mp parent) equal found
      · intro seen; cases seen with
        | nominal parent equal found => exact .nominal ((same _).mpr parent) equal found

theorem holds_observations (term : Expr Origin)
    (same : ∀ value, Observes model first value ↔ Observes model last value)
    (valid : Holds model term first) : Holds model term last := by
  induction term generalizing first last with
  | leaf origin =>
      obtain ⟨value,seen⟩ := valid.1
      exact ⟨⟨value,(same _).mp seen⟩,valid.2.1,fun a b one two => valid.2.2 a b ((same _).mpr one) two⟩
  | node test children ih =>
      obtain ⟨value,seen⟩ := valid.1.1
      exact ⟨⟨⟨value,(same _).mp seen⟩,fun value seen => valid.1.2 value ((same _).mpr seen)⟩,
        fun index => ih index (project_same_observations same test index) (valid.2 index)⟩

theorem holds_transport (same : Same model first last) (valid : Holds model term first) : Holds model term last := by
  cases term with
  | leaf origin => exact same_trans (same_symm same) valid
  | node test children =>
      obtain ⟨value,seen⟩ := same.1
      refine ⟨⟨same.2.1,fun other observed => test_transport test (same.2.2 value other seen observed) (valid.1.2 value seen)⟩,?_⟩
      intro index
      apply holds_observations (children index) _ (valid.2 index)
      intro value
      exact ⟨project_seen same test index,project_seen (same_symm same) test index⟩

theorem leaves_bind (term : Expr α) (substitution : α → Expr β) (leaf : β) :
    leaf ∈ (term.bind substitution).leaves ↔
      ∃ name ∈ term.leaves, leaf ∈ (substitution name).leaves := by
  induction term with
  | leaf name => simp [Expr.bind,Expr.leaves]
  | node test children ih =>
      simp only [Expr.bind,Expr.leaves,List.mem_flatten,List.mem_ofFn]
      constructor
      · rintro ⟨_,⟨index,rfl⟩,present⟩
        obtain ⟨name,member,present⟩ := (ih index).mp present
        exact ⟨name,⟨(children index).leaves,⟨index,rfl⟩,member⟩,present⟩
      · rintro ⟨name,⟨_,⟨index,rfl⟩,member⟩,present⟩
        exact ⟨_,⟨index,rfl⟩,(ih index).mpr ⟨name,member,present⟩⟩

/-- Every leaf use and constructor test must occur in the actual generated
schema. The certificate contains no output-value equality. -/
inductive Recipe (body : Schema) : Origin → Expr Nat → Prop
  | capture (root : Origin) (name : Nat) :
      (⟨name,root,.actual⟩ : Use) ∈ body.variables → Recipe body root (.leaf name)
  | node (root : Origin) (test : Test) (children : Fin (arity test) → Expr Nat) :
      (root,test) ∈ body.tests →
      (∀ index, Recipe body (project root test index) (children index)) →
      Recipe body root (.node test children)

theorem recipe_leaf_use (recipe : Recipe body root term) (member : name ∈ term.leaves) :
    ∃ origin, (⟨name,origin,.actual⟩ : Use) ∈ body.variables := by
  induction recipe with
  | capture root captured present =>
      have equal : name = captured := by simpa [Expr.leaves] using member
      subst name
      exact ⟨root,present⟩
  | node root test children present recipes ih =>
      simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn] at member
      obtain ⟨_,⟨index,rfl⟩,member⟩ := member
      exact ih index member

/-- Per-variable substitution is the additional semantic relation. Tests are
kept from the original schema; output terms are derived by Recipe induction. -/
def Coherent (model : Assignment) (body : Schema) (substitution : Nat → Expr Origin) : Prop :=
  (∀ test ∈ body.tests, Head model test.1 test.2) ∧
    ∀ entry ∈ body.variables, entry.mode = .actual → Holds model (substitution entry.name) entry.origin

theorem recipe_readback (recipe : Recipe body root term)
    (coherent : Coherent model body substitution) : Holds model (term.bind substitution) root := by
  induction recipe with
  | capture root name member => exact coherent.2 _ member rfl
  | node root test children member recipes ih =>
      exact ⟨coherent.1 _ member,ih⟩

/-- Substitution introduces no new leaves beyond the selected capture/child
terms. This is finite readback, with no bound on the depth of a leaf origin. -/
theorem readback_over (recipe : Recipe body root term)
    (coherent : Coherent model body substitution) (basis : List Origin)
    (closed : ∀ name ∈ term.leaves, ∀ origin ∈ (substitution name).leaves, origin ∈ basis) :
    Holds model (term.bind substitution) root ∧
      ∀ origin ∈ (term.bind substitution).leaves, origin ∈ basis := by
  refine ⟨recipe_readback recipe coherent,?_⟩
  intro origin member
  obtain ⟨name,present,member⟩ := (leaves_bind term substitution origin).mp member
  exact closed name present origin member

theorem packets_share (first : Coherent model firstBody firstSubstitution)
    (last : Coherent model lastBody lastSubstitution)
    (one : (⟨firstName,firstRoot,.actual⟩ : Use) ∈ firstBody.variables)
    (two : (⟨lastName,lastRoot,.actual⟩ : Use) ∈ lastBody.variables)
    (left : firstSubstitution firstName = .leaf shared)
    (right : lastSubstitution lastName = .leaf shared) : Same model firstRoot lastRoot := by
  have a := first.2 _ one rfl
  have b := last.2 _ two rfl
  rw [left] at a
  rw [right] at b
  exact same_trans a (same_symm b)

end Yulang.GeneralNominalOriginTerms
