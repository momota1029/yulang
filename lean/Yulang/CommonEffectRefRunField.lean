import Yulang.CommonEffectFieldTable

/-!
The actual rank-2 field signature from spec 4.6:
  run : forall f. (a -> [f] a) -> [e, f] ()
`a` and `e` are captured nominal arguments; `f` is a fresh row local. The
declaration stores finite syntax, not a semantic signature function. This
module does not infer the variance of `ref` or add a struct subtype rule.
-/
namespace Yulang.CommonEffectRefRunField
open Core.PresenceGeneration (Comp CompTerm TyTerm RowTerm)
open CommonEffectRequestGeneration (Computation Declarations)
open CommonEffectKindedFormula
open CommonEffectKindedGeneration
open CommonEffectRecursiveSource
open CommonEffectRecursiveGeneration (ContextRel)

variable {scopes : Nat}

def refRun (value effect : α) : FieldScheme α :=
  ⟨0, 1, .arrow
    (.arrow (.var (.inl value)) .empty (.var (.inl value)) (.var (.inr (.inr 0))))
    .empty (.base .unit) (.join (.var (.inl effect)) (.var (.inr (.inr 0))))⟩

def runType (value : Common.Ty) (captured fresh : Common.Row) : Common.Ty :=
  Common.arrow (Common.arrow value Common.rowEmpty value fresh) Common.rowEmpty
    (.base .unit) (Common.rowJoin captured fresh)

theorem refRun_wellKinded (value effect : α) : (refRun value effect).wellKinded = true := rfl

theorem refRun_eval (assignment : α → Computation) (value effect : α) (locals : Locals 0 1) :
    (refRun value effect).body.eval Common.model (localEnv assignment locals) =
      runType (assignment value).1 (assignment effect).2 (locals.effects 0) := rfl

/-- Creation is rigid in every Common row, including infinite rows and all
signed coordinates. The outer value/row captures and source body are fixed. -/
theorem construct_ref_run_exact (signatures : List SemanticSignature) (declarations : Declarations α)
    (environment : CommonEffectFormula.SchemeEnv scopes α) (bindings : List (Binding scopes))
    (assignment : α → Computation) (related : ContextRel signatures declarations assignment environment bindings)
    (value effect : α) (body : Expr scopes) :
    (constructCheckedField declarations environment (refRun value effect) body).Holds assignment ↔
      ∀ fresh : Common.Row, Typing signatures bindings body
        (Comp.pure Common.model (runType (assignment value).1 (assignment effect).2 fresh)) := by
  rw [construct_checked_field_exact signatures declarations environment bindings assignment related]
  simp only [refRun_wellKinded, true_and]
  change (∀ locals : Locals 0 1, Typing signatures bindings body
    (Comp.pure Common.model (runType (assignment value).1 (assignment effect).2 (locals.effects 0)))) ↔ _
  constructor
  · intro rigid fresh
    exact rigid ⟨Fin.elim0, fun _ => fresh⟩
  · intro rigid locals
    exact rigid (locals.effects 0)

/-- Each use chooses its own arbitrary Common row; the captured `e` is never
freshened along with `f`. No row-local condition is moved to the caller. -/
theorem use_ref_run_exact (assignment : α → Computation) (value effect : α) (out : CompTerm α) :
    (useCheckedField (scopes := scopes) (refRun value effect) out).Holds assignment ↔
      ∃ fresh : Common.Row, Comp.le Common.model
        (Comp.pure Common.model (runType (assignment value).1 (assignment effect).2 fresh))
        (out.eval Common.model assignment) := by
  rw [use_checked_field_exact]
  simp only [refRun_wellKinded, true_and]
  constructor
  · intro used
    cases used with
    | intro locals below =>
      exact ⟨locals.effects (⟨0, by decide⟩ : Fin 1), below⟩
  · rintro ⟨fresh, below⟩
    exact .intro (⟨Fin.elim0, fun _ => fresh⟩ : Locals 0 1) below

def declaration (value effect : α) (nominalName fieldName : Nat) :
    CommonEffectFieldTable.Declaration α :=
  ⟨nominalName, [⟨fieldName, refRun value effect⟩]⟩

/-- The resolved `ref` table has exactly the `run` field. Projection from that
table implements fresh row instantiation while retaining both outer captures. -/
theorem project_ref_run_exact (assignment : α → Computation) (value effect : α)
    (nominalName fieldName : Nat) (out : CompTerm α) :
    (CommonEffectFieldTable.project (scopes := scopes)
      (declaration value effect nominalName fieldName) 0 out).Holds assignment ↔
      ∃ fresh : Common.Row, Comp.le Common.model
        (Comp.pure Common.model (runType (assignment value).1 (assignment effect).2 fresh))
        (out.eval Common.model assignment) :=
  use_ref_run_exact assignment value effect out

end Yulang.CommonEffectRefRunField
