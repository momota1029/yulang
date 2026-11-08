import Yulang.CommonEffectFamilyArgumentKinds
import Yulang.CommonEffectMixedFamilyConstraints

/-!
Complete resolved family applications, before individual argument occurrences
are flattened for the interval allocator. The original ordered argument list
is retained, so an unknown zero-argument family or a missing suffix cannot
disappear from admission. Every emitted slot is computed from the application's
original row, family, and argument index; no slot-allocation oracle is supplied.

Family names and source row locations have already been resolved. The finite
family signatures describe invariant positions, not all nominal parameters.
-/
namespace Yulang.CommonEffectFamilyApplications
open CommonEffectMixedFamilyAllocation (Kind Argument Occurrence)
open CommonEffectFamilyArgumentKinds (ArgumentKinded checkArgument check_argument_exact)
open CommonEffectMixedFamilyConstraints (Families Declared)

structure Application (scopes : Nat) (α : Type) where
  row : Nat
  family : Nat
  origin : Nat
  arguments : List (Argument scopes α)

def checkArguments (kinds : α → Option Kind) : List Kind → List (Argument scopes α) → Bool
  | [], [] => true
  | kind :: signature, argument :: arguments =>
      (kind == argument.kind) && checkArgument kinds argument && checkArguments kinds signature arguments
  | _, _ => false

inductive ArgumentsAdmitted {scopes : Nat} {α : Type} (kinds : α → Option Kind) :
    List Kind → List (Argument scopes α) → Prop where
  | nil : ArgumentsAdmitted kinds [] []
  | cons : kind = argument.kind → ArgumentKinded kinds argument →
      ArgumentsAdmitted kinds signature arguments →
      ArgumentsAdmitted kinds (kind :: signature) (argument :: arguments)

theorem check_arguments_exact (kinds : α → Option Kind)
    (signature : List Kind) (arguments : List (Argument scopes α)) :
    checkArguments kinds signature arguments = true ↔ ArgumentsAdmitted kinds signature arguments := by
  induction signature generalizing arguments with
  | nil =>
    cases arguments with
    | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
    | cons argument arguments =>
      constructor
      · intro h; contradiction
      · intro h; cases h
  | cons kind signature ih =>
    cases arguments with
    | nil =>
      constructor
      · intro h; contradiction
      · intro h; cases h
    | cons argument arguments =>
      simp only [checkArguments, Bool.and_eq_true, beq_iff_eq, check_argument_exact, ih]
      exact ⟨fun ⟨⟨kinded, endpoints⟩, rest⟩ => .cons kinded endpoints rest,
        fun h => by cases h; exact ⟨⟨‹_›, ‹_›⟩, ‹_›⟩⟩

theorem ArgumentsAdmitted.length {kinds : α → Option Kind} {signature : List Kind}
    {arguments : List (Argument scopes α)} (admitted : ArgumentsAdmitted kinds signature arguments) :
    signature.length = arguments.length := by
  induction admitted with
  | nil => rfl
  | cons _ _ _ ih => exact congrArg Nat.succ ih

/-- The independent whole-list judgment exposes the same original position,
including its recursively checked endpoint names. -/
theorem ArgumentsAdmitted.at {kinds : α → Option Kind} {signature : List Kind}
    {arguments : List (Argument scopes α)} (admitted : ArgumentsAdmitted kinds signature arguments)
    (index : Fin arguments.length) :
    signature[index.val]? = some arguments[index].kind ∧
      ArgumentKinded kinds arguments[index] := by
  induction admitted with
  | nil => exact Fin.elim0 index
  | cons kinded endpoints rest ih =>
    cases index using Fin.cases with
    | zero => exact ⟨congrArg some kinded, endpoints⟩
    | succ index => exact ih index

def checkApplication (families : Families) (kinds : α → Option Kind)
    (application : Application scopes α) : Bool :=
  match families[application.family]? with
  | none => false
  | some signature => checkArguments kinds signature application.arguments

def Admitted (families : Families) (kinds : α → Option Kind)
    (application : Application scopes α) : Prop :=
  ∃ signature, families[application.family]? = some signature ∧
    ArgumentsAdmitted kinds signature application.arguments

/-- Exact arity, kind order, and endpoint names are computed even for an
application which will emit no argument occurrences. -/
theorem check_application_exact (families : Families) (kinds : α → Option Kind)
    (application : Application scopes α) :
    checkApplication families kinds application = true ↔ Admitted families kinds application := by
  cases found : families[application.family]? with
  | none => simp [checkApplication, found, Admitted]
  | some signature => simp [checkApplication, found, Admitted, check_arguments_exact]

def Application.at (application : Application scopes α) (index : Fin application.arguments.length) :
    Occurrence scopes α :=
  ⟨⟨application.row, application.family, index.val⟩, application.origin, application.arguments[index]⟩

def Application.occurrences (application : Application scopes α) : List (Occurrence scopes α) :=
  List.ofFn application.at

theorem Application.occurrences_length (application : Application scopes α) :
    application.occurrences.length = application.arguments.length := by
  simp only [Application.occurrences, List.length_ofFn]

def collect (applications : List (Application scopes α)) : List (Occurrence scopes α) :=
  applications.flatMap Application.occurrences

/-- Flattening preserves precisely all original application/argument
positions. Every row, family, origin, endpoint, and argument index is retained. -/
theorem collect_all_exact (applications : List (Application scopes α))
    (property : Occurrence scopes α → Prop) :
    (∀ occurrence ∈ collect applications, property occurrence) ↔
      ∀ application ∈ applications, ∀ index, property (application.at index) := by
  simp only [collect, List.forall_mem_flatMap, Application.occurrences]
  constructor
  · intro all application included index
    exact all application included (application.at index) (List.mem_ofFn.mpr ⟨index, rfl⟩)
  · intro all application included occurrence member
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
    exact all application included index

theorem Admitted.declared {families : Families} {kinds : α → Option Kind}
    {application : Application scopes α} (admitted : Admitted families kinds application)
    (index : Fin application.arguments.length) : Declared families (application.at index) := by
  obtain ⟨signature, found, arguments⟩ := admitted
  exact Declared.intro signature found (arguments.at index).1

theorem collect_declared (families : Families) (kinds : α → Option Kind)
    (applications : List (Application scopes α))
    (admitted : ∀ application ∈ applications, Admitted families kinds application) :
    ∀ occurrence ∈ collect applications, Declared families occurrence := by
  rw [collect_all_exact]
  exact fun application included index => (admitted application included).declared index

end Yulang.CommonEffectFamilyApplications
