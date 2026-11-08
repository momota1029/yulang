import Yulang.CommonEffectFamilyApplications

/-!
From complete resolved family applications to the actual mixed interval
allocator and ordinary generated constraints. Whole-application admission is
computed before flattening, so no missing family or missing argument becomes
vacuously valid. The independent semantics below retains the original list,
its full argument order, and shared actuals at precisely the original slots.

This is a source-application generation theorem, not quantified formula
elimination or source name/visibility resolution. No model/support/fuel
condition is placed on a returned scheme or its parameters.
-/
namespace Yulang.CommonEffectFamilyApplicationGeneration
open CommonEffectRequestGeneration (Computation)
open CommonEffectKindedFormula (Formula)
open CommonEffectMixedFamilyAllocation (Kind Slot)
open CommonEffectFamilyApplications
open CommonEffectMixedFamilyConstraints (Families argumentMember)

def FitsApplication (assignment : α → Computation) (values : Slot → Common.Ty)
    (effects : Slot → Common.Row) (application : Application scopes α) : Prop :=
  ∀ index : Fin application.arguments.length,
    argumentMember assignment
      (values ⟨application.row, application.family, index.val⟩,
       effects ⟨application.row, application.family, index.val⟩)
      application.arguments[index]

def Realizes (families : Families) (kinds : α → Option Kind)
    (applications : List (Application scopes α)) (assignment : α → Computation) : Prop :=
  ∃ values effects, ∀ application ∈ applications,
    Admitted families kinds application ∧ FitsApplication assignment values effects application

def generate (families : Families) (kinds : α → Option Kind)
    (applications : List (Application scopes α)) : Formula scopes α :=
  if applications.all (checkApplication families kinds) then
    CommonEffectMixedFamilyConstraints.generate families (collect applications)
  else .core .bot

/-- All original applications and all original endpoints are quantified.
Admission and exact arity are conclusions, not successful-check premises.
The finite actual-argument allocation is computed by the existing generator. -/
theorem generate_exact (families : Families) (kinds : α → Option Kind)
    (applications : List (Application scopes α)) (assignment : α → Computation) :
    (generate families kinds applications).Holds assignment ↔
      Realizes families kinds applications assignment := by
  by_cases admitted : applications.all (checkApplication families kinds) = true
  · have allAdmitted : ∀ application ∈ applications, Admitted families kinds application := by
      simpa only [List.all_eq_true, check_application_exact] using admitted
    simp only [generate, admitted, ↓reduceIte, CommonEffectMixedFamilyConstraints.generate_exact]
    constructor
    · rintro ⟨values, effects, members⟩
      have allMembers := (collect_all_exact applications
        (CommonEffectMixedFamilyConstraints.Member assignment values effects)).mp
          (fun occurrence included => (members occurrence included).2)
      exact ⟨values, effects, fun application included =>
        ⟨allAdmitted application included, allMembers application included⟩⟩
    · rintro ⟨values, effects, members⟩
      have allMembers := (collect_all_exact applications
        (CommonEffectMixedFamilyConstraints.Member assignment values effects)).mpr
          (fun application included => (members application included).2)
      exact ⟨values, effects, fun occurrence included =>
        ⟨collect_declared families kinds applications allAdmitted occurrence included,
          allMembers occurrence included⟩⟩
  · simp only [generate, admitted, Bool.false_eq_true, ↓reduceIte,
      Formula.holds_core, Core.PresenceGeneration.Formula.Holds, false_iff]
    rintro ⟨_, _, members⟩
    apply admitted
    simp only [List.all_eq_true, check_application_exact]
    exact fun application included => (members application included).1

/-- A finite captured-name table is used directly, with absent names still
absent. The producer does not receive a source-to-actual-slot callback. -/
def generateCaptured (families : Families) (captured : List Kind)
    (applications : List (Application scopes Nat)) : Formula scopes Nat :=
  generate families (fun name => captured[name]?) applications

theorem generate_captured_exact (families : Families) (captured : List Kind)
    (applications : List (Application scopes Nat)) (assignment : Nat → Computation) :
    (generateCaptured families captured applications).Holds assignment ↔
      Realizes families (fun name => captured[name]?) applications assignment :=
  generate_exact families (fun name => captured[name]?) applications assignment

/-- Even a nullary unknown application is rejected. Checking only emitted
argument occurrences would lose this source obligation. -/
theorem unknown_family_rejected (families : Families) (kinds : α → Option Kind)
    (applications : List (Application scopes α)) (assignment : α → Computation)
    (application : Application scopes α) (included : application ∈ applications)
    (missing : families[application.family]? = none) :
    ¬ (generate families kinds applications).Holds assignment := by
  intro holds
  obtain ⟨values, effects, realized⟩ := (generate_exact families kinds applications assignment).mp holds
  obtain ⟨signature, found, _⟩ := (realized application included).1
  simp [missing] at found

theorem wrong_arity_rejected (families : Families) (kinds : α → Option Kind)
    (applications : List (Application scopes α)) (assignment : α → Computation)
    (application : Application scopes α) (included : application ∈ applications)
    (signature : List Kind) (found : families[application.family]? = some signature)
    (wrong : signature.length ≠ application.arguments.length) :
    ¬ (generate families kinds applications).Holds assignment := by
  intro holds
  obtain ⟨values, effects, realized⟩ := (generate_exact families kinds applications assignment).mp holds
  obtain ⟨other, lookup, admitted⟩ := (realized application included).1
  have same : other = signature := Option.some.inj (lookup.symm.trans found)
  exact wrong (same ▸ admitted.length)

end Yulang.CommonEffectFamilyApplicationGeneration
