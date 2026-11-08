import Yulang.CommonEffectKindedFormula

/-!
Stored schemes and signed comparison helpers over the existing mixed-kind
formula syntax. These helpers do not introduce any semantic formula atom or
new binder; instantiation uses the capture-avoiding substitution already
proved for `CommonEffectKindedFormula.Formula`.
-/
namespace Yulang.CommonEffectKindedFormula
open Core.PresenceGeneration
open CommonEffectRequestGeneration (Computation RowExpr)

variable {scopes : Nat}

def Formula.core (body : Core.PresenceGeneration.Formula α) : Formula scopes α :=
  .old (.core body)

def Formula.rowLe (first last : RowExpr scopes α) : Formula scopes α :=
  .old (.rowLe first last)

def Formula.tyLe (first last : TyTerm α) : Formula scopes α := .core (.tyLe first last)
def Formula.compLe (first last : CompTerm α) : Formula scopes α := .core (.compLe first last)

@[simp] theorem Formula.holds_core (body : Core.PresenceGeneration.Formula α)
    (assignment : α → Computation) :
    (Formula.core (scopes := scopes) body).Holds assignment ↔ body.Holds Common.model assignment := Iff.rfl

@[simp] theorem Formula.holds_rowLe (first last : RowExpr scopes α) (assignment : α → Computation) :
    (Formula.rowLe first last).Holds assignment ↔ Common.rowLe (first.eval assignment) (last.eval assignment) := Iff.rfl

@[simp] theorem Formula.holds_compLe (first last : CompTerm α) (assignment : α → Computation) :
    (Formula.compLe (scopes := scopes) first last).Holds assignment ↔
      Comp.le Common.model (first.eval Common.model assignment) (last.eval Common.model assignment) := Iff.rfl

@[simp] theorem Formula.holds_tyLe (first last : TyTerm α) (assignment : α → Computation) :
    (Formula.tyLe (scopes := scopes) first last).Holds assignment ↔
      Common.Subtype (first.eval Common.model assignment) (last.eval Common.model assignment) := Iff.rfl

abbrev Scheme (scopes : Nat) (α : Type) := Formula scopes (Option α)
abbrev SchemeEnv (scopes : Nat) (α : Type) := List (Scheme scopes α)

def Scheme.instantiate (scheme : Scheme scopes α) (out : CompTerm α) : Formula scopes α :=
  scheme.subst (fun | none => out | some name => CompTerm.var name)

/-- Mixed universal locals in a stored value scheme stay bound while its
result slot is instantiated; the entire captured computation remains fixed. -/
@[simp] theorem Scheme.instantiate_exact (scheme : Scheme scopes α) (out : CompTerm α)
    (assignment : α → Computation) :
    (scheme.instantiate out).Holds assignment ↔ scheme.Holds (extend assignment (out.eval Common.model assignment)) := by
  simp only [instantiate, Formula.holds_subst]
  have same : (fun name => ((fun | none => out | some name => CompTerm.var name) name).eval Common.model assignment) =
      extend assignment (out.eval Common.model assignment) := by
    funext name
    cases name <;> rfl
  exact (congrArg (fun env => scheme.Holds env) same).to_iff

def Scheme.mono (input : CompTerm α) : Scheme scopes α :=
  Formula.compLe (input.rename some) (CompTerm.var none)

def SchemeEnv.rename (environment : SchemeEnv scopes α) (names : α → β) : SchemeEnv scopes β :=
  environment.map (Formula.rename (Option.map names))

def SchemeEnv.lift (environment : SchemeEnv scopes α) : SchemeEnv scopes (Option α) :=
  environment.rename some

def Scheme.lookup (environment : SchemeEnv scopes α) (index : Nat) (out : CompTerm α) : Formula scopes α :=
  match environment[index]? with
  | none => .core .bot
  | some scheme => scheme.instantiate out

@[simp] theorem Scheme.holds_mono (input : CompTerm α) (assignment : α → Computation) (out : Computation) :
    (Scheme.mono (scopes := scopes) input).Holds (extend assignment out) ↔
      Comp.le Common.model (input.eval Common.model assignment) out := by
  simp [mono]

def andAll (formulas : List (Formula scopes α)) : Formula scopes α :=
  formulas.foldr .and (.core .top)

@[simp] theorem andAll_exact (formulas : List (Formula scopes α)) (assignment : α → Computation) :
    (andAll formulas).Holds assignment ↔ ∀ formula ∈ formulas, formula.Holds assignment := by
  induction formulas <;> simp_all [andAll, Formula.Holds, Formula.core,
    CommonEffectFormula.Formula.Holds, Core.PresenceGeneration.Formula.Holds]

def env₂ (Γ : SchemeEnv scopes α) := Γ.lift.lift
def env₃ (Γ : SchemeEnv scopes α) := Γ.lift.lift.lift

end Yulang.CommonEffectKindedFormula
