import Yulang.CommonCanonicalBuilderPrograms
import Yulang.CanonicalRegisterRecognizer

/-!
# No computable exact canonical encoding for unrestricted finite row interfaces

The counterexample family uses finite symbolic unit/pair/union/general-arrow
interfaces, finite signed-row expressions, and finite closed recursive grid
rows. Row parameters retain their existing unrestricted Common.Row meaning.
The serializers encode syntax only. Both reduction compilers and their
composition with a hypothetical canonicalizer are actual finite programs.
-/

namespace Yulang.CommonCanonicalUndecidability

open CanonicalRegisterMachine
open CommonCanonicalRowSyntax
open CommonCanonicalSerialization
open CommonCanonicalCounterConstraints
open CommonCanonicalReductionMachine

/-- Equality of the existing public-instance families; parameter counts
are independent and assignments are unrestricted. -/
def PublicEquivalent (first last : Interface) : Prop :=
  ∀ theory : RoleConstraints.Theory model, ∀ target : Inference.Comp model,
    QualifiedInference.BindingTyping model theory first.binding target ↔
      QualifiedInference.BindingTyping model theory last.binding target

/-- Computability on valid finite syntax codes. No totality is demanded on
malformed natural inputs, and no semantic row predicate is an input code. -/
def ComputesEncoding (machine : Program) (encoding : Interface → Nat) : Prop :=
  ∀ interface, CanonicalRegisterMachine.Runs machine (interfaceCode interface) (encoding interface)

/-- E2 obstruction: even this finite symbolic subgrammar has no computable
canonical code whose equality is exactly the original public-instance
semantics. There is no compiler-realizability or invariant premise. -/
theorem no_computable_canonical_encoding :
    ¬ ∃ encoding : Interface → Nat, ∃ machine : Program,
      ComputesEncoding machine encoding ∧
      ∀ first last : Interface, PublicEquivalent first last ↔ encoding first = encoding last := by
  rintro ⟨encoding, machine, computes, exactness⟩
  obtain ⟨recognizer, recognizes⟩ := CanonicalRegisterRecognizer.recognizer_exact
    (builder false) (builder true) machine programCode
    (fun source => interfaceCode (targetInterface false source))
    (fun source => interfaceCode (targetInterface true source))
    (fun source => encoding (targetInterface false source))
    (fun source => encoding (targetInterface true source))
    (fun source => builder_program_runs source false)
    (fun source => builder_program_runs source true)
    (fun source => computes (targetInterface false source))
    (fun source => computes (targetInterface true source))
  apply no_nonhalting_semidecider programCode
  refine ⟨recognizer, fun source => ?_⟩
  have semantic : PublicEquivalent (targetInterface false source) (targetInterface true source) ↔
      ¬ Halts source (programCode source) :=
    public_instances_iff_nonhalting source (programCode source)
  exact (recognizes source).trans ((exactness _ _).symm.trans semantic)

/-- Empty obligations make the obstruction independent of the ambient role
registry. It already applies at any one fixed existing theory. -/
theorem no_computable_canonical_encoding_at_theory (theory : RoleConstraints.Theory model) :
    ¬ ∃ encoding : Interface → Nat, ∃ machine : Program,
      ComputesEncoding machine encoding ∧
      ∀ first last : Interface,
        (∀ target : Inference.Comp model,
          QualifiedInference.BindingTyping model theory first.binding target ↔
            QualifiedInference.BindingTyping model theory last.binding target) ↔ encoding first = encoding last := by
  rintro ⟨encoding, machine, computes, exactness⟩
  apply no_computable_canonical_encoding
  refine ⟨encoding, machine, computes, fun first last => ?_⟩
  have theoryIndependent : PublicEquivalent first last ↔
      (∀ target : Inference.Comp model,
        QualifiedInference.BindingTyping model theory first.binding target ↔
          QualifiedInference.BindingTyping model theory last.binding target) := by
    constructor
    · intro same target
      exact same theory target
    · intro same ambient target
      have atTheory := same target
      simpa only [binding_instances_exact] using atTheory
  exact theoryIndependent.trans (exactness first last)

end Yulang.CommonCanonicalUndecidability
