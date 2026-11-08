import Yulang.CommonEffectFamilyApplicationGeneration
import Yulang.CommonEffectMixedExact

/-!
The actual mixed recursive source generator and the complete family-argument
producer share one computed local binder. Operation declarations may refer to
those allocated value/row names in their input and output signatures. These
are the same names whose original application intervals are checked; the
declarations cannot silently obtain a second independent argument assignment.

The source declarations here use resolved, allocated references. Whole-source
name/visibility resolution, discovery of family applications, and elimination
of the resulting mixed quantifiers remain separate obligations.
-/
namespace Yulang.CommonEffectFamilySourceGeneration
open Core.PresenceGeneration (CompTerm)
open CommonEffectRequestGeneration (Computation)
open CommonEffectKindedFormula (Formula Names localEnv localEnv_comp_inl andAll andAll_exact)
open CommonEffectMixedKinds (Kind TypeKinded checkType check_type_exact nameKind)
open CommonEffectMixedDeclarations (Declaration Declarations interpretAll)
open CommonEffectMixedSource (Expr Typing)
open CommonEffectFamilyApplications (Application Admitted checkApplication check_application_exact collect collect_all_exact)
open CommonEffectFamilyApplicationGeneration (FitsApplication)
open CommonEffectMixedFamilyAllocation (slots Assignment valueAt rowAt)
open CommonEffectMixedFamilyConstraints (Families LocalNames Member emitOccurrence emitOccurrence_exact crosses crosses_of_members)

def localKinds (captured : α → Option Kind) : α ⊕ Names types rows → Option Kind
  | .inl name => captured name
  | .inr (.inl _) => some .value
  | .inr (.inr _) => some .row

def checkDeclaration (captured : α → Option Kind) (declaration : Declaration α) : Bool :=
  checkType (localKinds captured) declaration.input && checkType (localKinds captured) declaration.output

def DeclarationAdmitted (captured : α → Option Kind) (declaration : Declaration α) : Prop :=
  TypeKinded (localKinds captured) declaration.input ∧ TypeKinded (localKinds captured) declaration.output

def checkDeclarations (captured : α → Option Kind) (declarations : Declarations α) : Bool :=
  declarations.all (checkDeclaration captured)

def DeclarationsAdmitted (captured : α → Option Kind) (declarations : Declarations α) : Prop :=
  ∀ declaration ∈ declarations, DeclarationAdmitted captured declaration

theorem check_declarations_exact (captured : α → Option Kind) (declarations : Declarations α) :
    checkDeclarations captured declarations = true ↔ DeclarationsAdmitted captured declarations := by
  simp only [checkDeclarations, List.all_eq_true, checkDeclaration, Bool.and_eq_true,
    check_type_exact, DeclarationsAdmitted, DeclarationAdmitted]

abbrev FamilyNames (applications : List (Application scopes Nat)) := LocalNames (collect applications)

def emitApplications (applications : List (Application scopes Nat)) : Formula scopes (FamilyNames applications) :=
  andAll ((collect applications).map (emitOccurrence (collect applications)))

theorem emit_applications_exact (applications : List (Application scopes Nat))
    (assignment : Nat → Computation) (locals : Assignment (collect applications)) :
    (emitApplications applications).Holds (localEnv assignment locals) ↔
      ∀ application ∈ applications,
        FitsApplication assignment (valueAt (collect applications) locals)
          (rowAt (collect applications) locals) application := by
  simp only [emitApplications, andAll_exact, List.forall_mem_map]
  constructor
  · intro held
    apply (collect_all_exact applications
      (Member assignment (valueAt (collect applications) locals) (rowAt (collect applications) locals))).mp
    exact fun occurrence included => (emitOccurrence_exact _ occurrence included assignment locals).mp
      (held occurrence included)
  · intro fits occurrence included
    apply (emitOccurrence_exact _ occurrence included assignment locals).mpr
    exact (collect_all_exact applications
      (Member assignment (valueAt (collect applications) locals) (rowAt (collect applications) locals))).mpr
        fits occurrence included

private theorem closed_source_exact (applications : List (Application scopes Nat))
    (declarations : Declarations (FamilyNames applications)) (body : Expr scopes) (out : CompTerm Nat)
    (assignment : Nat → Computation) (locals : Assignment (collect applications)) :
    (CommonEffectMixedGeneration.generate declarations [] body (out.rename Sum.inl)).Holds
      (localEnv assignment locals) ↔
      Typing (interpretAll (localEnv assignment locals) declarations) [] body
        (out.eval Common.model assignment) := by
  simpa only [CompTerm.eval_rename, localEnv_comp_inl] using
    CommonEffectMixedExact.generate_recursive_mixed_exact
      (interpretAll (localEnv assignment locals) declarations) body [] [] (localEnv assignment locals)
      (out.rename Sum.inl) ⟨rfl, CommonEffectMixedGeneration.EnvRel.nil _ _⟩

def generate (captured : List Kind) (families : Families)
    (applications : List (Application scopes Nat))
    (declarations : Declarations (FamilyNames applications)) (body : Expr scopes) (out : CompTerm Nat) :
    Formula scopes Nat :=
  if applications.all (checkApplication families (fun name => captured[name]?)) &&
      checkDeclarations (nameKind captured) declarations then
    .and (crosses (collect applications))
      (.existsLocals (slots .value (collect applications)).length (slots .row (collect applications)).length
        (.and (emitApplications applications)
          (CommonEffectMixedGeneration.generate declarations [] body (out.rename Sum.inl))))
  else .core .bot

/-- Independent source typing uses the same original body and declarations,
the same shared arguments, and an outer result fixed before all local binders.
The declarations' operation-local binders remain inside their own source rules. -/
def Realizes (captured : List Kind) (families : Families)
    (applications : List (Application scopes Nat))
    (declarations : Declarations (FamilyNames applications)) (body : Expr scopes) (out : CompTerm Nat)
    (assignment : Nat → Computation) : Prop :=
  (∀ application ∈ applications, Admitted families (fun name => captured[name]?) application) ∧
  DeclarationsAdmitted (nameKind captured) declarations ∧
  ∃ locals : Assignment (collect applications),
    (∀ application ∈ applications,
      FitsApplication assignment (valueAt (collect applications) locals)
        (rowAt (collect applications) locals) application) ∧
    Typing (interpretAll (localEnv assignment locals) declarations) [] body
      (out.eval Common.model assignment)

/-- Whole application checks, both local kinds, every original endpoint and
the recursive mixed source judgment are connected under one actual binder.
No successful check, caller-selected body typing, support, or fuel is assumed. -/
theorem generate_exact (captured : List Kind) (families : Families)
    (applications : List (Application scopes Nat))
    (declarations : Declarations (FamilyNames applications)) (body : Expr scopes) (out : CompTerm Nat)
    (assignment : Nat → Computation) :
    (generate captured families applications declarations body out).Holds assignment ↔
      Realizes captured families applications declarations body out assignment := by
  by_cases admitted : (applications.all (checkApplication families (fun name => captured[name]?)) &&
      checkDeclarations (nameKind captured) declarations) = true
  · have admittedParts : applications.all (checkApplication families (fun name => captured[name]?)) = true ∧
        checkDeclarations (nameKind captured) declarations = true := by
      simpa only [Bool.and_eq_true] using admitted
    have apps : ∀ application ∈ applications,
        Admitted families (fun name => captured[name]?) application := by
      simpa only [List.all_eq_true, check_application_exact] using admittedParts.1
    have decls := (check_declarations_exact (nameKind captured) declarations).mp admittedParts.2
    simp only [generate, admitted, ↓reduceIte, Formula.Holds]
    constructor
    · rintro ⟨_, locals, intervals, source⟩
      exact ⟨apps, decls, locals, (emit_applications_exact applications assignment locals).mp intervals,
        (closed_source_exact applications declarations body out assignment locals).mp source⟩
    · rintro ⟨_, _, locals, fits, typed⟩
      have members := (collect_all_exact applications
        (Member assignment (valueAt (collect applications) locals) (rowAt (collect applications) locals))).mpr fits
      exact ⟨crosses_of_members (collect applications) assignment
        (valueAt (collect applications) locals) (rowAt (collect applications) locals) members,
        locals, (emit_applications_exact applications assignment locals).mpr fits,
        (closed_source_exact applications declarations body out assignment locals).mpr typed⟩
  · simp only [generate, admitted, Bool.false_eq_true, ↓reduceIte, Formula.holds_core,
      Core.PresenceGeneration.Formula.Holds, false_iff]
    rintro ⟨apps, decls, _⟩
    apply admitted
    rw [Bool.and_eq_true]
    constructor
    · simpa only [List.all_eq_true, check_application_exact] using apps
    · exact (check_declarations_exact (nameKind captured) declarations).mpr decls

end Yulang.CommonEffectFamilySourceGeneration
