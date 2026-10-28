import YulangClosure.SourcePrincipalTransport
import YulangClosure.Contracts

/-!
Boundary countermodels for the two uninstantiated original principality inputs.

The source is the EXISTING `SourcePrincipalTransport.hCall` at its complete
recursive-body context. Its certificate cannot be derived from the other
fields of `OriginalSource.Kernel`: two records which agree on all those fields
give opposite judgments for this same source. These records are models of the
checked interface, NOT claimed original Yulang semantic interpretations. In
particular no W/Z arm is removed, made empty, or identified with the structural
Call image. The original declaration which interprets the certificate remains
the missing semantic input.

The second countermodel keeps a single `SourceProblem`, source/solution
coverage, and the principal predicate fixed. Two reflexive/transitive instance
relations give opposite `PrincipalCoverage` results. Thus solution-set coverage
cannot determine the original principal ordering. Neither countermodel refutes
the original Yulang theorem or source-qualifies a native rejection.
-/
namespace YulangClosure.OriginalPrincipalityResolution

open OriginalSource

namespace CallBoundary

open SourcePrincipalTransport

def certificateAtom : Atom :=
  atom .completeCallCertificate 16 bodyContext [17, 18]

/-- Inversion at the actual original existential view telescope. All original
environment data is retained in the child; no earlier/future event is chosen. -/
theorem h_call_requires_certificate {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value)
    (typed : SourceJudgment kernel environment bodyContext hCall) :
    ∃ candidate : ScopedValue Value,
      kernel.admitted environment ⟨16, .viewLogic, 0⟩ candidate ∧
      kernel.atom (environment.extend ⟨16, .viewLogic, 0⟩ candidate)
        certificateAtom := by
  unfold SourceJudgment at typed
  rw [h_call_complete_rule] at typed
  cases typed with
  | existsE candidate admitted body =>
      cases body with
      | rule locals children =>
          have localCertificate := locals (.atom certificateAtom) (by
            simp [certificateAtom])
          cases localCertificate with
          | atom evidence => exact ⟨candidate, admitted, evidence⟩

/-- A complete instance of the currently declared *interface*. Only the
certificate atom depends on `certificate`; the original source syntax, every
environment coordinate and all other local fields are identical. The trivial
other meanings are deliberate countermodel data, not Yulang semantic laws. -/
def kernel (Value : Type) (certificate : Prop) : Kernel Value where
  atom := fun _ value =>
    match value.kind with
    | .completeCallCertificate => certificate
    | _ => True
  admitted := fun _ _ _ => True
  primitiveCheck := fun _ _ _ => True
  structuralShape := fun _ _ _ _ => True
  functionShape := fun _ _ _ _ _ => True
  boundaryTag := fun _ _ _ _ _ _ => True
  conversion := fun _ _ _ _ _ _ => True
  checkingAdmitted := fun _ _ _ _ => True

theorem other_atoms_fixed {Value : Type} (first second : Prop)
    (environment : Environment Value) (value : Atom)
    (other : value.kind ≠ .completeCallCertificate) :
    (kernel Value first).atom environment value ↔
      (kernel Value second).atom environment value := by
  cases kind : value.kind <;> simp_all [kernel]

/-- Even checking admission, which is separate from source admission, agrees.
These are equal functions on their full original dependent arguments. -/
theorem other_kernel_fields_fixed (Value : Type) (first second : Prop) :
    (kernel Value first).admitted = (kernel Value second).admitted ∧
    (kernel Value first).primitiveCheck = (kernel Value second).primitiveCheck ∧
    (kernel Value first).structuralShape = (kernel Value second).structuralShape ∧
    (kernel Value first).functionShape = (kernel Value second).functionShape ∧
    (kernel Value first).boundaryTag = (kernel Value second).boundaryTag ∧
    (kernel Value first).conversion = (kernel Value second).conversion ∧
    (kernel Value first).checkingAdmitted = (kernel Value second).checkingAdmitted :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem local_when_certificate {Value : Type} {certificate : Prop}
    (present : certificate) (environment : Environment Value) (premise : Premise) :
    Local (kernel Value certificate) environment premise := by
  cases premise with
  | atom value =>
      apply Local.atom
      cases kind : value.kind <;> simp only [kernel, kind] <;>
        first | exact present | exact True.intro
  | checking goal => exact .checking (.primitive goal 0 True.intro)
  | boundary site context lower upper =>
      exact .boundary (.actual site context lower upper 0 True.intro)

private theorem names_when_certificate {Value : Type} {certificate : Prop}
    (present : certificate) (environment : Environment Value) :
    SourceJudgment (kernel Value certificate) environment bodyContext hName ∧
    SourceJudgment (kernel Value certificate) environment bodyContext xName := by
  constructor <;>
    unfold SourceJudgment <;>
    simp only [hName, xName, sourceRules] <;>
    apply Judgment.rule <;>
    first
    | exact fun premise _ => local_when_certificate present environment premise
    | exact Judgments.nil

/-- Exact dependence of the SAME original h x judgment on the missing atom.
This is an interface separation, not an interpretation of complete Call. -/
theorem h_call_iff_certificate {Value : Type} (certificate : Prop)
    (environment : Environment Value) :
    SourceJudgment (kernel Value certificate) environment bodyContext hCall ↔
      certificate := by
  constructor
  · intro typed
    obtain ⟨candidate, _, evidence⟩ :=
      h_call_requires_certificate (kernel Value certificate) environment typed
    exact evidence
  · intro present
    unfold SourceJudgment
    rw [h_call_complete_rule]
    let candidate : ScopedValue Value :=
      ⟨environment.root, ⟨environment.eventPath, 0⟩⟩
    apply Judgment.existsE candidate True.intro
    apply Judgment.rule
    · exact fun premise _ => local_when_certificate present _ premise
    · obtain ⟨callee, argument⟩ := names_when_certificate present
        (environment.extend ⟨16, .viewLogic, 0⟩ candidate)
      exact .cons callee (.cons argument .nil)

/-- Both concrete kernels have the entire original interface. Their sole
changed atom gives opposite answers for the existing actual source App. -/
theorem opposite_h_call_judgments {Value : Type} (environment : Environment Value) :
    SourceJudgment (kernel Value True) environment bodyContext hCall ∧
      ¬ SourceJudgment (kernel Value False) environment bodyContext hCall := by
  exact ⟨(h_call_iff_certificate True environment).mpr True.intro,
    (h_call_iff_certificate False environment).mp⟩

end CallBoundary

namespace OrderBoundary

/-- Interface countermodel only. Both witnesses/solutions remain available;
there is no selection of a smaller original Yulang language or semantics. -/
def problem : SourceProblem Unit Unit Unit Bool Unit Bool Unit where
  supported := fun _ => True
  sourceJudgment := fun _ _ _ => True
  coreJudgment := fun _ _ _ => True
  elaborates := fun _ _ => True
  sameObservations := fun _ _ _ _ => True
  generates := fun _ _ _ => True
  solves := fun _ _ => True
  sameScoped := fun _ _ witness solution => witness = solution
  nativeStep := fun _ _ => False
  nativeRealizes := fun _ _ _ => True
  nativeSuccess := fun _ _ _ => True
  inferInitial := fun _ _ _ => True
  inferStep := fun _ _ => False

def principal : Unit → Unit → Unit → Bool → Prop := fun _ _ _ _ => True
def indiscrete : Unit → Bool → Bool → Prop := fun _ _ _ => True
def discrete : Unit → Bool → Bool → Prop := fun _ first second => first = second

theorem same_problem_sound_and_complete :
    problem.InferenceSoundness ∧ problem.SourceScopedCoverage := by
  constructor
  · intro source scope constraint solution _ _ _
    exact ⟨solution, True.intro, rfl⟩
  · intro source scope witness constraint _ _ _
    exact ⟨witness, True.intro, rfl⟩

theorem both_instance_relations_preorders :
    (∀ scope first, indiscrete scope first first) ∧
    (∀ scope first second third, indiscrete scope first second →
      indiscrete scope second third → indiscrete scope first third) ∧
    (∀ scope first, discrete scope first first) ∧
    (∀ scope first second third, discrete scope first second →
      discrete scope second third → discrete scope first third) :=
  ⟨fun _ _ => True.intro, fun _ _ _ _ _ _ => True.intro,
    fun _ _ => rfl, fun _ _ _ _ first second => first.trans second⟩

theorem indiscrete_principal : problem.PrincipalCoverage principal indiscrete := by
  intro source scope constraint _ _ _
  refine ⟨false, True.intro, True.intro, ?_⟩
  intro witness _
  exact ⟨witness, True.intro, rfl, True.intro⟩

theorem not_discrete_principal : ¬ problem.PrincipalCoverage principal discrete := by
  intro coverage
  obtain ⟨solution, _, _, covers⟩ :=
    coverage () () () True.intro True.intro ⟨false, True.intro⟩
  obtain ⟨first, _, firstScoped, firstInstance⟩ := covers false True.intro
  obtain ⟨second, _, secondScoped, secondInstance⟩ := covers true True.intro
  have firstSame : false = first := firstScoped
  have secondSame : true = second := secondScoped
  have equal : first = second := firstInstance.symm.trans secondInstance
  have impossible : false = true := firstSame.trans (equal.trans secondSame.symm)
  cases impossible

/-- Identical source/solution data and a fixed principal predicate do not
determine principality, even after requiring both candidate orders to be
reflexive and transitive. The missing original order must be instantiated. -/
theorem coverage_does_not_determine_principality :
    problem.SourceScopedCoverage ∧
      problem.PrincipalCoverage principal indiscrete ∧
      ¬ problem.PrincipalCoverage principal discrete :=
  ⟨same_problem_sound_and_complete.2, indiscrete_principal, not_discrete_principal⟩

end OrderBoundary

end YulangClosure.OriginalPrincipalityResolution
