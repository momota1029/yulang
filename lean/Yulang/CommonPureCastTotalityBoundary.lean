import Yulang.CommonNominalFullGuardedClosure
import Yulang.CoreCommonSyntax
import Yulang.EvaluationReads
import Yulang.PureCasts

/-!
# A typed pure strict source body cannot always become a total pure plan

This is an obstruction to the existing well-founded PureCasts representation,
not to every possible implementation of the original B5 contract. The exact
strict lambda fragment is mapped to existing CBV runtime syntax. Historical
Core.app is never treated as strictApp. No general Core evaluator, effect
soundness theorem, or source termination assumption is supplied.
-/

namespace Yulang.CommonPureCastTotalityBoundary

open CommonNominalFullCarrier

/-- A strict source fragment; its source and runtime maps retain every node. -/
inductive Fragment where
  | var : Nat → Fragment
  | lam : Fragment → Fragment
  | app : Fragment → Fragment → Fragment
  deriving DecidableEq, Repr

def Fragment.source : Fragment → Core.CommonSyntax.Term
  | .var index => .var index
  | .lam body => .lam body.source
  | .app function argument => .strictApp function.source argument.source

def Fragment.runtime (globals : Nat) : Fragment → EvaluationOrder.Expr globals
  | .var index => .bound index
  | .lam body => .lam (body.runtime globals)
  | .app function argument => .app (function.runtime globals) (argument.runtime globals)

def delta : Fragment := .lam (.app (.var 0) (.var 0))
def omega : Fragment := .app delta delta

def loopBody : CommonNominalFullGuardedClosure.Body 1 1 :=
  fun _ => .arrow (.inl 0) Common.rowEmpty (.inr 0) Common.rowEmpty

def loop (result : Ty) : Ty :=
  CommonNominalFullGuardedClosure.instantiate loopBody (fun _ => result) 0

theorem loop_unfold (result : Ty) :
    Equivalent (loop result) (arrow (loop result) Common.rowEmpty result Common.rowEmpty) :=
  CommonNominalFullGuardedClosure.all_parameter_sound loopBody (fun _ => result) 0

private theorem strict_body_typed
    (environment : List (Core.CommonSyntax.Binding model)) (result : Ty) :
    Core.CommonSyntax.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model (loop result)) :: environment)
      (.strictApp (.var 0) (.var 0)) (Core.PresenceGeneration.Comp.pure model result) := by
  have argument : Core.CommonSyntax.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model (loop result)) :: environment)
      (.var 0) (Core.PresenceGeneration.Comp.pure model (loop result)) :=
    .var rfl (.mono ⟨subtype_refl _, Common.rowLe_refl _⟩)
  have function : Core.CommonSyntax.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model (loop result)) :: environment)
      (.var 0) (Core.PresenceGeneration.Comp.pure model
        (arrow (loop result) Common.rowEmpty result Common.rowEmpty)) :=
    .var rfl (.mono ⟨(loop_unfold result).1, Common.rowLe_refl _⟩)
  refine Core.CommonSyntax.Typing.strictApp
    (a := Core.PresenceGeneration.Comp.pure model (loop result))
    (b := Core.PresenceGeneration.Comp.pure model result)
    (actual := Core.PresenceGeneration.Comp.pure model (loop result))
    (ef := Common.rowEmpty) function argument ⟨subtype_refl _, Common.rowLe_refl _⟩ ?_
  exact ⟨subtype_refl _, fun _ impossible =>
    impossible.elim False.elim (fun impossible => impossible.elim False.elim False.elim)⟩

/-- Every captured environment and every result type in the full regular
nominal carrier. The actual source judgment, not an assumed body certificate. -/
theorem omega_typed (environment : List (Core.CommonSyntax.Binding model)) (result : Ty) :
    Core.CommonSyntax.Typing model environment omega.source
      (Core.PresenceGeneration.Comp.pure model result) := by
  have argument : Core.CommonSyntax.Typing model environment delta.source
      (Core.PresenceGeneration.Comp.pure model (loop result)) :=
    .lam (strict_body_typed environment result) ⟨(loop_unfold result).2, Common.rowLe_refl _⟩
  have function : Core.CommonSyntax.Typing model environment delta.source
      (Core.PresenceGeneration.Comp.pure model
        (arrow (loop result) Common.rowEmpty result Common.rowEmpty)) :=
    .lam (strict_body_typed environment result) ⟨subtype_refl _, Common.rowLe_refl _⟩
  refine Core.CommonSyntax.Typing.strictApp
    (a := Core.PresenceGeneration.Comp.pure model (loop result))
    (b := Core.PresenceGeneration.Comp.pure model result)
    (actual := Core.PresenceGeneration.Comp.pure model (loop result))
    (ef := Common.rowEmpty) function argument ⟨subtype_refl _, Common.rowLe_refl _⟩ ?_
  exact ⟨subtype_refl _, fun _ impossible =>
    impossible.elim False.elim (fun impossible => impossible.elim False.elim False.elim)⟩

theorem unit_bool_body_typed :
    Core.CommonSyntax.Typing model
      [.mono (Core.PresenceGeneration.Comp.pure model (.base .unit))] omega.source
      (Core.PresenceGeneration.Comp.pure model (.base .bool)) := omega_typed _ _

open EvaluationOrder EvaluationSafety

private def selfBody : EvaluationOrder.Expr n := .app (.bound 0) (.bound 0)

private theorem selfBody_no_eval {n : Nat} (program : Program n) (store : Store n)
    (captured : List (Value n)) {environment : List (Value n)} {expression : EvaluationOrder.Expr n}
    {result : Value n} {reads : List (Fin n)}
    (evaluation : Eval program store environment expression result reads) :
    environment = .closure selfBody captured :: captured → expression = selfBody → False := by
  induction evaluation with
  | @app environment fn body lexical fnReads arg argument argReads result bodyReads
      fnEval argEval bodyEval fnIH argIH bodyIH =>
      intro sameEnv sameExpression
      have parts : fn = .bound 0 ∧ arg = .bound 0 := by
        simpa [selfBody] using sameExpression
      rcases parts with ⟨rfl, rfl⟩
      subst environment
      cases fnEval with
      | bound found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Value.closure.injEq] at found
          rcases found with ⟨rfl, rfl⟩
          cases argEval with
          | bound found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst argument
              exact bodyIH rfl rfl
  | _ => intro _ impossible; cases impossible

/-- Actual existing finite CBV evaluation, for arbitrary programs, stores and
captured values. Neither fuel nor a termination premise is used. -/
theorem omega_no_eval {n : Nat} (program : Program n) (store : Store n)
    (captured : List (Value n)) (result : Value n) (reads : List (Fin n)) :
    ¬ Eval program store captured (omega.runtime n) result reads := by
  intro evaluated
  cases evaluated with
  | app function argument body =>
      cases function with
      | closure =>
          cases argument with
          | closure => exact selfBody_no_eval program store captured body rfl rfl

/-- Even the weak direction 'the plan returned, so its source body has some
finite return evaluation' cannot hold for a total PureCasts plan of this body.
No representation or correspondence of the returned value is required. -/
theorem no_faithful_total_plan {n globals : Nat} {Key Payload Response A B : Type}
    (program : Program globals) (store : Store globals)
    (captured : List (Value globals)) (input : A) :
    ¬ ∃ plan : PureCasts.Plan n Key Payload Response A B,
      ∀ returned, plan.run input = .pure returned →
        ∃ result reads, Eval program store captured (omega.runtime globals) result reads := by
  rintro ⟨plan, faithful⟩
  obtain ⟨result, reads, evaluated⟩ := faithful (plan.value input) (plan.run_eq_pure input)
  exact omega_no_eval program store captured result reads evaluated

end Yulang.CommonPureCastTotalityBoundary
