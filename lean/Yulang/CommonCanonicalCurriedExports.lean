import Yulang.CommonCanonicalCurriedFamilies
import Yulang.CommonCanonicalArrowExports

/-!
# Complete public-instance codes for fixed-depth curried arrows

The actual `QualifiedInference.Interface` receives every argument's shared
generalized slot, both of its fixed row IDs, and the scalar result with its
captured/generalized distinction unchanged. Its existing binding and scheme
meanings are exactly the mixed-polarity family already proved complete.

The argument count is arbitrary but equal on the two sides. Generalized
counts and sharing patterns are unrestricted. Obligations are empty, and
ambient type/row assignments and target computations are fully quantified.
The final EOF lemma retains the real raw-support check; unlike the separate
one-arrow EOF-code theorem, this file does not compare partial exportability
by a combined support-and-family code. No inference readback or renderer is
introduced here.
-/

namespace Yulang.CommonCanonicalCurriedExports

open CommonCanonicalCurriedTransfer (Scheme Instances spine)
open CommonCanonicalCurriedFamilies (canonicalEncoding)
open CommonCanonicalArrowExports (model Ambient toOutput)
open Inference (Comp TyTerm RowTerm)
open QualifiedInference (Interface BindingTyping slotEnv)

variable {fixed rowSlots arguments generalized other : Nat}

def toSpine : (count : Nat) → (Fin count → TyTerm α) → (Fin count → RowTerm α) →
    (Fin count → RowTerm α) → TyTerm α → TyTerm α
  | 0, _, _, _, output => output
  | count + 1, inputs, incoming, outgoing, output =>
      .arrow (inputs 0) (incoming 0)
        (toSpine count (fun index => inputs index.succ) (fun index => incoming index.succ)
          (fun index => outgoing index.succ) output) (outgoing 0)

theorem toSpine_eval (count : Nat) (inputs : Fin count → TyTerm α)
    (incoming outgoing : Fin count → RowTerm α) (output : TyTerm α) (environment : α → Comp model) :
    (toSpine count inputs incoming outgoing output).eval model environment =
      spine count (fun index => (inputs index).eval model environment)
        (fun index => (incoming index).eval model environment)
        (fun index => (outgoing index).eval model environment) (output.eval model environment) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [toSpine, TyTerm.eval, spine, ih]
      rfl

def toValue (scheme : Scheme fixed rowSlots arguments generalized) : TyTerm (Ambient fixed rowSlots ⊕ Fin generalized) :=
  toSpine arguments (fun position => .var (.inr (scheme.input position)))
    (fun position => .var (.inl (.inr (scheme.incoming position))))
    (fun position => .var (.inl (.inr (scheme.outgoing position)))) (toOutput scheme.output)

def toInterface (scheme : Scheme fixed rowSlots arguments generalized) : Interface (Ambient fixed rowSlots) generalized :=
  ⟨toValue scheme, []⟩

theorem toValue_eval (scheme : Scheme fixed rowSlots arguments generalized)
    (ambient : Ambient fixed rowSlots → Comp model) (parameters : Fin generalized → Comp model) :
    (toValue scheme).eval model (slotEnv ambient parameters) =
      CommonCanonicalCurriedTransfer.instantiate scheme (fun index => (ambient (.inr index)).2)
        (fun index => (ambient (.inl index)).1) (fun index => (parameters index).1) := by
  rw [toValue, toSpine_eval, CommonCanonicalArrowExports.toOutput_eval]
  rfl

theorem binding_instances_exact (scheme : Scheme fixed rowSlots arguments generalized)
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

theorem scheme_instances_exact (scheme : Scheme fixed rowSlots arguments generalized)
    (theory : RoleConstraints.Theory model) (ambient : Ambient fixed rowSlots → Comp model) (target : Comp model) :
    (toInterface scheme).scheme.Holds model theory (Inference.extend ambient target) ↔
      Instances scheme (fun index => (ambient (.inr index)).2) (fun index => (ambient (.inl index)).1) target.1 :=
  (Interface.scheme_exact model theory ambient (toInterface scheme) target).trans
    (binding_instances_exact scheme theory ambient target)

/-- Complete canonicality for the existing public-instance meaning at any
fixed curried depth, across arbitrary local arities and all sharing patterns.
Ambient identities are shared; the arrow rows remain ambient row slots. -/
theorem interface_canonicalEncoding_exact (first : Scheme fixed rowSlots arguments generalized)
    (last : Scheme fixed rowSlots arguments other) :
    (∀ theory : RoleConstraints.Theory model, ∀ ambient : Ambient fixed rowSlots → Comp model, ∀ target : Comp model,
      (toInterface first).scheme.Holds model theory (Inference.extend ambient target) ↔
        (toInterface last).scheme.Holds model theory (Inference.extend ambient target)) ↔
      canonicalEncoding first = canonicalEncoding last := by
  rw [← CommonCanonicalCurriedFamilies.canonicalEncoding_exact]
  constructor
  · intro same rows captured target
    have observed := same (fun _ => False)
      (Sum.elim (fun index => (captured index, Common.rowEmpty)) (fun index => (.bottom, rows index)))
      (target, Common.rowEmpty)
    simpa only [scheme_instances_exact, Sum.elim_inl, Sum.elim_inr] using observed
  · intro same theory ambient target
    rw [scheme_instances_exact, scheme_instances_exact]
    exact same (fun index => (ambient (.inr index)).2) (fun index => (ambient (.inl index)).1) target.1

theorem finishModule_exact (scheme : Scheme fixed rowSlots arguments generalized)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : Ambient fixed rowSlots → Option (Comp model))
    (closed : QualifiedInference.ClosedInterface model generalized) :
    QualifiedInference.finishModule model decode impls wf assignment (toInterface scheme) = some closed ↔
      (toInterface scheme).known assignment = true ∧
        (toInterface scheme).closeAt model (QualifiedInference.completeAssignment model assignment) = closed := by
  rw [QualifiedInference.finishModule_exact]
  simp [toInterface, QualifiedInference.pending, RoleConstraints.Satisfies]

end Yulang.CommonCanonicalCurriedExports
