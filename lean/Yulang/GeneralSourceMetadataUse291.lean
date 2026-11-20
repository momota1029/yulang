import Yulang.GeneralSourceMetadataFixture291

/-! A use asks for both constructor identity and argument arity. Merely
checking the catalogue or the nominal flag does not materialize row layouts. -/
namespace Yulang.GeneralSourceMetadataUse291
open GeneralNominalCenteredHeadWFSource (ConstructorUse)
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)

abbrev Use := Nat × Nat

def supported (c : Constructors) (i : Interpretation) (u : Use) : Bool :=
  match c u.1 with
  | none => false
  | some decl => decide (decl.parameters.length = u.2) &&
      ((match i.primitives u.1 with
        | none => false
        | some p => decide (decl.parameters = p.parameters)) ||
       (i.invariantNominal u.1 && decide (decl.parameters = List.replicate u.2 .type)))

theorem supported_exact (c : Constructors) (i : Interpretation) (key arity : Nat) :
    supported c i (key,arity) = true ↔ ConstructorUse c i key arity := by
  unfold supported ConstructorUse
  cases c key with
  | none => simp
  | some d =>
    cases i.primitives key <;> simp

def UsesOK (c : Constructors) (i : Interpretation) (uses : List Use) : Prop :=
  ∀ u ∈ uses, ConstructorUse c i u.1 u.2

def check (c : Constructors) (i : Interpretation) (uses : List Use) : Bool :=
  uses.all (supported c i)

theorem check_exact (c : Constructors) (i : Interpretation) (uses : List Use) :
    check c i uses = true ↔ UsesOK c i uses := by
  unfold check UsesOK
  rw [List.all_eq_true]
  exact ⟨fun h u p => (supported_exact c i u.1 u.2).mp (h u p),
    fun h u p => (supported_exact c i u.1 u.2).mpr (h u p)⟩

theorem use_append (c : Constructors) (i : Interpretation) (a b : List Use) :
    UsesOK c i (a ++ b) ↔ UsesOK c i a ∧ UsesOK c i b := by
  simp only [UsesOK,List.mem_append,or_imp,forall_and]

theorem use_cons (c : Constructors) (i : Interpretation) (x : Use) (xs : List Use) :
    UsesOK c i (x :: xs) ↔ ConstructorUse c i x.1 x.2 ∧ UsesOK c i xs := by
  simp only [UsesOK,List.mem_cons,or_imp,forall_and,forall_eq]

theorem use_flatMap {α : Type} (c : Constructors) (i : Interpretation) (items : List α)
    (f : α → List Use) : UsesOK c i (items.flatMap f) ↔ ∀ a ∈ items, UsesOK c i (f a) := by
  constructor
  · intro whole a member u k
    exact whole u (List.mem_flatMap.mpr ⟨a,member,k⟩)
  · intro each u belongs
    obtain ⟨a,member,k⟩ := List.mem_flatMap.mp belongs
    exact each a member u k

end Yulang.GeneralSourceMetadataUse291
