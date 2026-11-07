import Yulang.Common
import Yulang.ModuleRoles

/-!
# Uniform qualified-family inclusion by finite supplied evidence

The public meaning below is the existing `Interface.scheme.Holds`. Comparing
it in every caller theory is equivalent to transporting each source assignment
to a destination assignment whose value is below the source value and whose
qualifiers all occur among the source qualifiers. The least caller theory for
one assignment is membership in that assignment's finite qualifier list.

This is a characterization, not a decision procedure or a canonical encoding.
It treats the entire existing `QualifiedInference.Interface` grammar, including
nonempty qualifiers, arbitrary type/row sharing and different local arities.
That grammar still lacks default/mask, symbolic regular blocks and nominal
heads. Ambient-only pending obligations remain the separate existing EOF gate;
they are not silently inserted into or removed from the public scheme meaning.
-/

namespace Yulang.CommonCanonicalQualifiedFamilies

open Inference (Comp)
open QualifiedInference (Interface BindingTyping slotEnv qualifiers)
open RoleConstraints (Theory Goal Satisfies)

abbrev model := Common.model.toModel

variable {α : Type} {n k : Nat}

/-- This exact criterion quantifies over all assignments, not merely finite
samples or bijective renamings. Predicate membership is literal membership in
the existing evidence semantics; no congruence of arbitrary theories is assumed. -/
theorem interface_inclusion_iff (first : Interface α n) (last : Interface α k) :
    (∀ theory : Theory model, ∀ ambient : α → Comp model, ∀ target : Comp model,
      first.scheme.Holds model theory (Inference.extend ambient target) →
        last.scheme.Holds model theory (Inference.extend ambient target)) ↔
    (∀ ambient : α → Comp model, ∀ parameters : Fin n → Comp model,
      ∃ replacement : Fin k → Comp model,
        (∀ goal ∈ (qualifiers last.obligations).map (Goal.eval model (slotEnv ambient replacement)),
          goal ∈ (qualifiers first.obligations).map (Goal.eval model (slotEnv ambient parameters))) ∧
        Common.Subtype (last.value.eval model (slotEnv ambient replacement))
          (first.value.eval model (slotEnv ambient parameters))) := by
  constructor
  · intro included ambient parameters
    let evidence := (qualifiers first.obligations).map (Goal.eval model (slotEnv ambient parameters))
    let theory : Theory model := fun goal => goal ∈ evidence
    let target := Comp.pure model (first.value.eval model (slotEnv ambient parameters))
    have source : first.scheme.Holds model theory (Inference.extend ambient target) := by
      rw [Interface.scheme_exact, Interface.binding, BindingTyping.qualified_iff]
      exact ⟨parameters, fun _ member => member,
        Common.subtype_refl _, Common.rowLe_refl _⟩
    have destination := included theory ambient target source
    rw [Interface.scheme_exact, Interface.binding, BindingTyping.qualified_iff] at destination
    obtain ⟨replacement, supplied, below⟩ := destination
    exact ⟨replacement, supplied, below.1⟩
  · intro transport theory ambient target source
    rw [Interface.scheme_exact, Interface.binding, BindingTyping.qualified_iff] at source ⊢
    obtain ⟨parameters, supplied, below⟩ := source
    obtain ⟨replacement, subset, valueBelow⟩ := transport ambient parameters
    exact ⟨replacement, fun goal member => supplied goal (subset goal member),
      Common.subtype_trans valueBelow below.1, below.2⟩

/-- Independent transport in each direction permits different local arities
and noninvertible, assignment-dependent witnesses. It does not assert that a
finite syntactic substitution implements those witnesses. -/
def WitnessTransport (first : Interface α n) (last : Interface α k) : Prop :=
  ∀ ambient : α → Comp model, ∀ parameters : Fin n → Comp model,
    ∃ replacement : Fin k → Comp model,
      (∀ goal ∈ (qualifiers last.obligations).map (Goal.eval model (slotEnv ambient replacement)),
        goal ∈ (qualifiers first.obligations).map (Goal.eval model (slotEnv ambient parameters))) ∧
      Common.Subtype (last.value.eval model (slotEnv ambient replacement))
        (first.value.eval model (slotEnv ambient parameters))

theorem interface_equivalent_iff (first : Interface α n) (last : Interface α k) :
    (∀ theory : Theory model, ∀ ambient : α → Comp model, ∀ target : Comp model,
      first.scheme.Holds model theory (Inference.extend ambient target) ↔
        last.scheme.Holds model theory (Inference.extend ambient target)) ↔
      WitnessTransport first last ∧ WitnessTransport last first := by
  constructor
  · intro same
    exact ⟨(interface_inclusion_iff first last).mp (fun theory ambient target => (same theory ambient target).mp),
      (interface_inclusion_iff last first).mp (fun theory ambient target => (same theory ambient target).mpr)⟩
  · rintro ⟨forward, backward⟩ theory ambient target
    exact ⟨(interface_inclusion_iff first last).mpr forward theory ambient target,
      (interface_inclusion_iff last first).mpr backward theory ambient target⟩

/-- Actual EOF finalization followed by use of its returned binding. Pending
evidence uses the file's resolver; qualifiers use the caller's theory. -/
def FinishedInstances (interface : Interface α n)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp model)) (theory : Theory model) (target : Comp model) : Prop :=
  ∃ closed : QualifiedInference.ClosedInterface model n,
    QualifiedInference.finishModule model decode impls wf assignment interface = some closed ∧
      BindingTyping model theory
        (.qualified n closed.requirements (fun parameters => Comp.pure model (closed.value parameters))) target

/-- No successful-export or known-slot hypothesis: the actual failure cases
remain on the right, independently of public family equivalence. This covers
nonempty pending and lifted obligations throughout the old interface grammar. -/
theorem finished_instances_exact (interface : Interface α n)
    (decode : model.Ty → Roles.Term) (impls : List Roles.Impl) (wf : Roles.WellFormed impls)
    (assignment : α → Option (Comp model)) (theory : Theory model) (target : Comp model) :
    FinishedInstances interface decode impls wf assignment theory target ↔
      interface.known assignment = true ∧
      Satisfies (RoleConstraints.resolvingTheory decode impls)
        ((QualifiedInference.pending interface.obligations).map
          (Goal.eval model (QualifiedInference.completeAssignment model assignment))) ∧
      interface.scheme.Holds model theory
        (Inference.extend (QualifiedInference.completeAssignment model assignment) target) := by
  rw [Interface.scheme_exact]
  constructor
  · rintro ⟨closed, accepted, typed⟩
    obtain ⟨known, pending, same⟩ :=
      (QualifiedInference.finishModule_exact model decode impls wf assignment interface closed).mp accepted
    subst closed
    exact ⟨known, pending, typed⟩
  · rintro ⟨known, pending, typed⟩
    refine ⟨interface.closeAt model (QualifiedInference.completeAssignment model assignment), ?_, typed⟩
    exact (QualifiedInference.finishModule_exact model decode impls wf assignment interface _).mpr
      ⟨known, pending, rfl⟩

end Yulang.CommonCanonicalQualifiedFamilies
