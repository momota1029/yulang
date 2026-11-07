import Yulang.CommonCanonicalArrowFamilies
import Yulang.CommonCanonicalScalarExports

/-!
# Shared-arrow family codes for the existing public interface

The complete arrow language is translated into the actual
`QualifiedInference.Interface`, with separate finite captured-type and row
identities in its ambient context. Generalized computation parameters are
quantified by the existing binding and scheme rules; their unused row parts
are unrestricted. The local obligations and ambient-only pending list are
empty in this fragment.

The main canonicality theorem uses `Interface.scheme.Holds` itself, with
arbitrary role theory, total ambient computation assignment and target. The
EOF theorem below retains the actual raw-support check on partial ambient
assignments. Ordinary instance-code equality alone is not asserted to
preserve that separate check, nor to provide readback from `Core.infer`.
-/

namespace Yulang.CommonCanonicalArrowExports

open ProducerCanonicalOpen (Expr)
open CommonCanonicalArrowFamilies (Scheme Instances canonicalEncoding)
open Inference (Comp TyTerm RowTerm)
open QualifiedInference (Interface BindingTyping slotEnv)

variable {fixed rowSlots generalized other : Nat}

abbrev model := Common.model.toModel
abbrev Ambient (fixed rowSlots : Nat) := Fin fixed ⊕ Fin rowSlots

def toOutput (expression : Expr (fixed + generalized)) : TyTerm (Ambient fixed rowSlots ⊕ Fin generalized) :=
  (CommonCanonicalScalarExports.toValue expression).rename (Sum.map Sum.inl id)

def toValue (scheme : Scheme fixed rowSlots generalized) : TyTerm (Ambient fixed rowSlots ⊕ Fin generalized) :=
  .arrow (.var (.inr scheme.input)) (.var (.inl (.inr scheme.incoming)))
    (toOutput scheme.output) (.var (.inl (.inr scheme.outgoing)))

def toInterface (scheme : Scheme fixed rowSlots generalized) : Interface (Ambient fixed rowSlots) generalized :=
  ⟨toValue scheme, []⟩

theorem toOutput_eval (expression : Expr (fixed + generalized))
    (ambient : Ambient fixed rowSlots → Comp model) (parameters : Fin generalized → Comp model) :
    (toOutput expression).eval model (slotEnv ambient parameters) =
      CommonCanonicalOpen.instantiate
        (Fin.addCases (fun index => (ambient (.inl index)).1) (fun index => (parameters index).1)) expression := by
  have renamed : slotEnv ambient parameters ∘ Sum.map Sum.inl id =
      slotEnv (fun index => ambient (.inl index)) parameters := by
    funext index
    cases index <;> rfl
  rw [toOutput, TyTerm.eval_rename, renamed, CommonCanonicalScalarExports.toValue_eval]
  rfl

theorem toValue_eval (scheme : Scheme fixed rowSlots generalized)
    (ambient : Ambient fixed rowSlots → Comp model) (parameters : Fin generalized → Comp model) :
    (toValue scheme).eval model (slotEnv ambient parameters) =
      CommonCanonicalArrowFamilies.instantiate scheme (fun index => (ambient (.inr index)).2)
        (fun index => (ambient (.inl index)).1) (fun index => (parameters index).1) := by
  change Common.arrow (parameters scheme.input).1 (ambient (.inr scheme.incoming)).2
    ((toOutput scheme.output).eval model (slotEnv ambient parameters)) (ambient (.inr scheme.outgoing)).2 = _
  rw [toOutput_eval]
  rfl

theorem binding_instances_exact (scheme : Scheme fixed rowSlots generalized)
    (theory : RoleConstraints.Theory model) (ambient : Ambient fixed rowSlots → Comp model) (target : Comp model) :
    BindingTyping model theory ((toInterface scheme).binding model ambient) target ↔
      Instances scheme (fun index => (ambient (.inr index)).2) (fun index => (ambient (.inl index)).1) target.1 := by
  change BindingTyping model theory
    (.qualified generalized (fun _ => [])
      (fun parameters => Comp.pure model ((toValue scheme).eval model (slotEnv ambient parameters)))) target ↔ _
  rw [BindingTyping.qualified_iff]
  constructor
  · rintro ⟨parameters, _, below⟩
    refine ⟨fun index => (parameters index).1, ?_⟩
    have value := below.1
    change Common.Subtype ((toValue scheme).eval model (slotEnv ambient parameters)) target.1 at value
    rw [toValue_eval] at value
    exact value
  · rintro ⟨parameters, below⟩
    refine ⟨fun index => (parameters index, Common.rowEmpty), by simp [RoleConstraints.Satisfies], ?_⟩
    refine ⟨?_, Common.rowEmpty_le target.2⟩
    change Common.Subtype
      ((toValue scheme).eval model (slotEnv ambient (fun index => (parameters index, Common.rowEmpty)))) target.1
    rw [toValue_eval]
    exact below

theorem scheme_instances_exact (scheme : Scheme fixed rowSlots generalized)
    (theory : RoleConstraints.Theory model) (ambient : Ambient fixed rowSlots → Comp model) (target : Comp model) :
    (toInterface scheme).scheme.Holds model theory (Inference.extend ambient target) ↔
      Instances scheme (fun index => (ambient (.inr index)).2) (fun index => (ambient (.inl index)).1) target.1 :=
  (Interface.scheme_exact model theory ambient (toInterface scheme) target).trans
    (binding_instances_exact scheme theory ambient target)

/-- All fixed slot counts, both generalized arities, row identities, role
theories, ambient assignments and targets are quantified. The semantics on
the left is the existing public scheme meaning, without a new alpha relation. -/
theorem interface_canonicalEncoding_exact (first : Scheme fixed rowSlots generalized) (last : Scheme fixed rowSlots other) :
    (∀ theory : RoleConstraints.Theory model, ∀ ambient : Ambient fixed rowSlots → Comp model, ∀ target : Comp model,
      (toInterface first).scheme.Holds model theory (Inference.extend ambient target) ↔
        (toInterface last).scheme.Holds model theory (Inference.extend ambient target)) ↔
      canonicalEncoding first = canonicalEncoding last := by
  rw [← CommonCanonicalArrowFamilies.canonicalEncoding_exact]
  constructor
  · intro same rows captured target
    have observed := same (fun _ => False)
      (Sum.elim (fun index => (captured index, Common.rowEmpty)) (fun index => (.bottom, rows index)))
      (target, Common.rowEmpty)
    simpa only [scheme_instances_exact, Sum.elim_inl, Sum.elim_inr] using observed
  · intro same theory ambient target
    rw [scheme_instances_exact, scheme_instances_exact]
    exact same (fun index => (ambient (.inr index)).2) (fun index => (ambient (.inl index)).1) target.1

/-- Even an unqualified interface has a real EOF support check. Pending role
resolution is vacuous here; unresolved captured or row slots are not erased. -/
theorem finishModule_exact (scheme : Scheme fixed rowSlots generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient fixed rowSlots → Option (Comp model))
    (closed : QualifiedInference.ClosedInterface model generalized) :
    QualifiedInference.finishModule model decode impls wf assignment (toInterface scheme) = some closed ↔
      (toInterface scheme).known assignment = true ∧
        (toInterface scheme).closeAt model (QualifiedInference.completeAssignment model assignment) = closed := by
  rw [QualifiedInference.finishModule_exact]
  simp [toInterface, QualifiedInference.pending, RoleConstraints.Satisfies]

end Yulang.CommonCanonicalArrowExports
