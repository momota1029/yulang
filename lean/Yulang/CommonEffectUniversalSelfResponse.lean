import Yulang.CommonEffectUniversalResumption

/-! A computed universal elimination for any finite family of self-response
signatures, including arbitrary finite type bodies and local-variable counts.
The source arm is `k payload`. Other source arm shapes remain separate. -/
namespace Yulang.CommonEffectUniversalSelfResponse
open Core.PresenceGeneration
open CommonEffectRequestGeneration
open CommonEffectArmGeneration (generateArms generate_arms_exact)
open CommonEffectUniversalResumption (resume_payload_iff)

/-- Actual finite syntax; input and response share the same written body. -/
structure Declaration (α : Type) where
  locals : Nat
  key : Nat
  extra : List Nat := []
  body : TyTerm (α ⊕ Fin locals)

def Declaration.toOperation (declaration : Declaration α) : CommonEffectRequestGeneration.Declaration α :=
  ⟨declaration.locals, declaration.key, declaration.extra, declaration.body, declaration.body⟩

/-- Every finite family, arbitrary declaration bodies/local counts, arbitrary
captured environment and rows. Zero arms contribute no additional bound. -/
theorem generate_self_response_arms_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (declarations : Fin count → Declaration α) (input out : CompTerm α) :
    (generateArms (scopes := scopes) environment (fun i => (declarations i).toOperation)
      input out (fun _ => .app (.var 1) (.var 0))).Holds assignment ↔
      count = 0 ∨ Comp.le Common.model (input.eval Common.model assignment) (out.eval Common.model assignment) := by
  rw [generate_arms_exact environment bindings assignment related]
  simp only [Declaration.toOperation]
  constructor
  · intro universal
    by_cases empty : count = 0
    · exact Or.inl empty
    · apply Or.inr
      let index : Fin count := ⟨0, Nat.pos_of_ne_zero empty⟩
      obtain ⟨operated, valid⟩ := universal (fun _ _ => .top)
      have resumed := (resume_payload_iff bindings
        ((declarations index).body.eval Common.model (localEnv assignment (fun _ => .top)))
        (input.eval Common.model assignment) (operated index)).mp (valid index).1
      exact ⟨Common.subtype_trans resumed.1 (valid index).2.1,
        Common.rowLe_trans resumed.2 (valid index).2.2⟩
  · rintro (empty | bound) locals
    · subst count
      exact ⟨fun index => Fin.elim0 index, fun index => Fin.elim0 index⟩
    · refine ⟨fun _ => input.eval Common.model assignment, fun index => ⟨?_, bound⟩⟩
      apply (resume_payload_iff bindings
        ((declarations index).body.eval Common.model (localEnv assignment (locals index)))
        (input.eval Common.model assignment) _).mpr
      exact ⟨Common.subtype_refl _, Common.rowLe_refl _⟩

/-- This algorithm outputs a finite ordinary comparison, never forallTypes. -/
def eliminate (count : Nat) (input out : CompTerm α) : CommonEffectFormula.Formula scopes α :=
  if count = 0 then .core .top else .compLe input out

/-- No verification of infinitely many local assignments is a premise or a
remaining condition on parameters. The comparison retains the original row. -/
theorem eliminate_exact (environment : SchemeEnv α) (bindings : List (Binding Common.model))
    (assignment : α → Computation) (related : EnvRel Common.model assignment environment bindings)
    (declarations : Fin count → Declaration α) (input out : CompTerm α) :
    (generateArms (scopes := scopes) environment (fun i => (declarations i).toOperation)
      input out (fun _ => .app (.var 1) (.var 0))).Holds assignment ↔
      (eliminate (scopes := scopes) count input out).Holds assignment := by
  rw [generate_self_response_arms_exact environment bindings assignment related]
  by_cases empty : count = 0
  · simp [eliminate, empty, CommonEffectFormula.Formula.Holds, Formula.Holds]
  · simp [eliminate, empty]
end Yulang.CommonEffectUniversalSelfResponse
