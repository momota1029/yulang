import Yulang.CommonCanonicalScalarFamilies
import Yulang.ModuleRoles
import Yulang.CommonRigidHeadInspection

/-!
# Scalar family codes for the actual finite public interface syntax

The adapter below constructs an existing `QualifiedInference.Interface` with
its original ambient/generalized slot distinction and no role obligations.
Its meaning is the existing `Interface.scheme.Holds` / `BindingTyping`, using
the common model. Equality of canonical codes is equivalent to equality of
that public instance meaning, across arbitrary generalized arities and every
fixed ambient assignment, including the zero-slot cases.

No alternative definition of the public interface's meaning is introduced.
The scalar fragment has no intrinsic row expressions or role requirements.
The final examples explain why separately normalizing covariant scalar
leaves cannot extend this result to shared negative occurrences, or discard
a role requirement attached only to a generalized output parameter.
-/

namespace Yulang.CommonCanonicalScalarExports

open ProducerCanonicalOpen (Expr)
open CommonCanonicalOpen (instantiate)
open CommonCanonicalScalarFamilies (environment Instances FamilyEquivalent canonicalEncoding)
open Inference (Comp TyTerm)
open QualifiedInference (Interface BindingTyping slotEnv)

variable {weak generalized other : Nat}

abbrev model := Common.model.toModel

def toValue : Expr (weak + generalized) → TyTerm (Fin weak ⊕ Fin generalized)
  | .atom (.var index) => .var (Fin.addCases Sum.inl Sum.inr index)
  | .atom (.base scalar) => .base scalar
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (toValue first) (toValue last)
  | .inter first last => .inter (toValue first) (toValue last)

def toInterface (expression : Expr (weak + generalized)) : Interface (Fin weak) generalized :=
  ⟨toValue expression, []⟩

theorem toValue_eval (expression : Expr (weak + generalized))
    (ambient : Fin weak → Comp model) (parameters : Fin generalized → Comp model) :
    (toValue expression).eval model (slotEnv ambient parameters) =
      instantiate (environment (fun index => (ambient index).1) (fun index => (parameters index).1)) expression := by
  induction expression with
  | atom entry =>
      cases entry with
      | var index =>
          refine Fin.addCases ?_ ?_ index
          · intro index
            simp only [toValue, TyTerm.eval, Fin.addCases_left, slotEnv, Sum.elim_inl,
              instantiate, CommonCanonicalOpen.atomType, environment]
            exact (Fin.addCases_left (motive := fun _ => Common.Ty)
              (left := fun i => (ambient i).1) (right := fun i => (parameters i).1) index).symm
          · intro index
            simp only [toValue, TyTerm.eval, Fin.addCases_right, slotEnv, Sum.elim_inr,
              instantiate, CommonCanonicalOpen.atomType, environment]
            exact (Fin.addCases_right (motive := fun _ => Common.Ty)
              (left := fun i => (ambient i).1) (right := fun i => (parameters i).1) index).symm
      | base => rfl
  | bottom | top => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      simp only [toValue, TyTerm.eval, instantiate, ihf, ihl]
      rfl

/-- Row parameters are quantified by the existing public binding semantics.
They do not occur in this scalar value, and the value itself is pure. -/
theorem binding_instances_exact (expression : Expr (weak + generalized))
    (theory : RoleConstraints.Theory model) (ambient : Fin weak → Comp model) (target : Comp model) :
    BindingTyping model theory ((toInterface expression).binding model ambient) target ↔
      Instances expression (fun index => (ambient index).1) target.1 := by
  change BindingTyping model theory
    (.qualified generalized (fun _ => [])
      (fun parameters => Comp.pure model ((toValue expression).eval model (slotEnv ambient parameters)))) target ↔ _
  rw [BindingTyping.qualified_iff]
  constructor
  · rintro ⟨parameters, _, below⟩
    refine ⟨fun index => (parameters index).1, ?_⟩
    have value := below.1
    change Common.Subtype ((toValue expression).eval model (slotEnv ambient parameters)) target.1 at value
    rw [toValue_eval] at value
    exact value
  · rintro ⟨parameters, below⟩
    refine ⟨fun index => (parameters index, Common.rowEmpty), by simp [RoleConstraints.Satisfies], ?_⟩
    refine ⟨?_, Common.rowEmpty_le target.2⟩
    change Common.Subtype
      ((toValue expression).eval model (slotEnv ambient (fun index => (parameters index, Common.rowEmpty)))) target.1
    rw [toValue_eval]
    exact below

theorem scheme_instances_exact (expression : Expr (weak + generalized))
    (theory : RoleConstraints.Theory model) (ambient : Fin weak → Comp model) (target : Comp model) :
    (toInterface expression).scheme.Holds model theory (Inference.extend ambient target) ↔
      Instances expression (fun index => (ambient index).1) target.1 :=
  (Interface.scheme_exact model theory ambient (toInterface expression) target).trans
    (binding_instances_exact expression theory ambient target)

/-- Complete for the actual unqualified scalar public-interface fragment:
generalized arities may differ and every ambient type/row assignment is fixed
on both sides. No same-arity permutation relation replaces `scheme.Holds`. -/
theorem interface_canonicalEncoding_exact (first : Expr (weak + generalized)) (last : Expr (weak + other)) :
    (∀ theory : RoleConstraints.Theory model, ∀ ambient : Fin weak → Comp model, ∀ target : Comp model,
      (toInterface first).scheme.Holds model theory (Inference.extend ambient target) ↔
        (toInterface last).scheme.Holds model theory (Inference.extend ambient target)) ↔
      canonicalEncoding first = canonicalEncoding last := by
  rw [← CommonCanonicalScalarFamilies.canonicalEncoding_exact]
  constructor
  · intro same ambient target
    have observed := same (fun _ => False) (fun index => (ambient index, Common.rowEmpty))
      (target, Common.rowEmpty)
    simpa only [scheme_instances_exact] using observed
  · intro same theory ambient target
    rw [scheme_instances_exact, scheme_instances_exact]
    exact same (fun index => (ambient index).1) target.1

namespace Examples

open CommonCanonicalInterface (Form)

def sharedArrow : Form 1 := .arrow 0 0 (.atom (.var 0)) (.scalar (.atom (.var 0)))
def independentArrow : Form 2 := .arrow 0 0 (.atom (.var 0)) (.scalar (.atom (.var 1)))

/-- Shared positive/negative occurrences express a relation between whole
argument and result types, even though each individual leaf is scalar. -/
theorem shared_arrow_instances_iff (input output : Common.Ty) :
    (∃ parameters : Fin 1 → Common.Ty,
      Common.Subtype (sharedArrow.instantiate (fun _ => Common.rowEmpty) parameters)
        (Common.arrow input Common.rowEmpty output Common.rowEmpty)) ↔
      Common.Subtype input output := by
  constructor
  · rintro ⟨parameters, below⟩
    have parts := (Common.common_arrow_iff _ _ _ _ _ _ _ _).mp below
    exact Common.subtype_trans parts.1 parts.2.2.1
  · intro below
    refine ⟨fun _ => input, ?_⟩
    exact (Common.common_arrow_iff _ _ _ _ _ _ _ _).mpr
      ⟨Common.subtype_refl _, Common.rowLe_refl _, below, Common.rowLe_refl _⟩

theorem independent_arrow_instances (input output : Common.Ty) :
    ∃ parameters : Fin 2 → Common.Ty,
      Common.Subtype (independentArrow.instantiate (fun _ => Common.rowEmpty) parameters)
        (Common.arrow input Common.rowEmpty output Common.rowEmpty) := by
  refine ⟨fun index => if index = 0 then input else output, ?_⟩
  have same : independentArrow.instantiate (fun _ => Common.rowEmpty)
      (fun index => if index = 0 then input else output) =
      Common.arrow input Common.rowEmpty output Common.rowEmpty := by
    simp [independentArrow, Form.instantiate, instantiate, CommonCanonicalOpen.atomType]
  rw [same]
  exact Common.subtype_refl _

/-- The concrete target distinguishes the two instance families. Ignoring
cross-polarity sharing would incorrectly identify these public types. -/
theorem negative_sharing_cannot_be_split :
    ¬ (∃ parameters : Fin 1 → Common.Ty,
      Common.Subtype (sharedArrow.instantiate (fun _ => Common.rowEmpty) parameters)
        (Common.arrow (.base .int) Common.rowEmpty (.base .str) Common.rowEmpty)) ∧
      (∃ parameters : Fin 2 → Common.Ty,
      Common.Subtype (independentArrow.instantiate (fun _ => Common.rowEmpty) parameters)
        (Common.arrow (.base .int) Common.rowEmpty (.base .str) Common.rowEmpty)) := by
  refine ⟨?_, independent_arrow_instances _ _⟩
  intro member
  have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp
    ((shared_arrow_instances_iff _ _).mp member)
  cases impossible

def qualifiedOutput : Interface (Fin 0) 1 :=
  ⟨.var (.inr 0), [⟨0, [.var (.inr 0)]⟩]⟩

def intOnlyTheory : RoleConstraints.Theory model :=
  fun goal => goal = ⟨0, [.base .int]⟩

/-- A role attached only to the positive output still restricts that
generalized parameter. The actual qualifier interpretation retains it. -/
theorem qualified_output_instances_iff (target : Common.Ty) :
    BindingTyping model intOnlyTheory (qualifiedOutput.binding model Fin.elim0)
        (target, Common.rowEmpty) ↔ Common.Subtype (.base .int) target := by
  change BindingTyping model intOnlyTheory
    (.qualified 1 (fun parameters => [⟨0, [(parameters 0).1]⟩])
      (fun parameters => ((parameters 0).1, Common.rowEmpty))) (target, Common.rowEmpty) ↔ _
  rw [BindingTyping.qualified_iff]
  constructor
  · rintro ⟨parameters, evidence, below⟩
    have chosen := evidence ⟨0, [(parameters 0).1]⟩ (by simp)
    have argument := congrArg RoleConstraints.Predicate.args chosen
    have valueSame : (parameters 0).1 = (.base .int : Common.Ty) := (List.cons.inj argument).1
    have valueBelow := below.1
    change Common.Subtype (parameters 0).1 target at valueBelow
    exact valueSame ▸ valueBelow
  · intro below
    refine ⟨fun _ => ((.base .int : Common.Ty), Common.rowEmpty), ?_, below, Common.rowLe_refl _⟩
    simp [RoleConstraints.Satisfies, intOnlyTheory]

/-- Removing a qualifier is unsound even when its variable appears only in
the output. This is independent of the cross-polarity sharing obstruction. -/
theorem positive_role_cannot_be_erased :
    ¬ BindingTyping model intOnlyTheory (qualifiedOutput.binding model Fin.elim0)
        ((.base .str : Common.Ty), Common.rowEmpty) ∧
      BindingTyping model intOnlyTheory
        ((toInterface (weak := 0) (generalized := 1) (.atom (.var 0))).binding model Fin.elim0)
        ((.base .str : Common.Ty), Common.rowEmpty) := by
  refine ⟨?_, ?_⟩
  · intro typed
    have impossible := (CommonRigidHeadInspection.base_iff .int .str).mp
      ((qualified_output_instances_iff _).mp typed)
    cases impossible
  · apply (binding_instances_exact _ intOnlyTheory Fin.elim0 _).mpr
    exact ⟨fun _ => .bottom, CommonBoundCoalescing.bottom_le _⟩

end Examples

end Yulang.CommonCanonicalScalarExports
