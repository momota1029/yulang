import Yulang.CommonAlignedPatternGeneration
import Yulang.CommonPatternGenerationProvenance
import Yulang.CommonAlignedPatternGenerationProvenance

/-! A local optional-input field rule, kept separate from the existing
required-input source rule. Adopting it in full source case typing awaits
notes/questions/2026-11-07-b2-optional-field-case-pattern.md. Both children
retain the established independent structural judgment and Q4 scopes. -/

namespace Yulang.CommonOptionalField

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration (renameBindings evalTypes_rename evalTypes_take evalTypes_drop)
open CommonAlignedPatternTyping (RawTyping)
open CommonDefaultRequired (OptionalPayload)
open CasePatterns (Pattern)

inductive Typing (DefaultTyped : NamedTypes → D → Common.Ty → Prop)
    (types : NamedTypes) (name : Nat) (p rest : Pattern Empty D) (input : Common.Ty) : NamedTypes → Prop where
  | field {original payload : Common.Ty} {left right : NamedTypes} :
      Common.Subtype input original → OptionalPayload name original payload →
      RawTyping DefaultTyped types p payload left → RawTyping DefaultTyped (left ++ types) rest original right →
      Typing DefaultTyped types name p rest input (left ++ right)

theorem Typing.binding_names (typed : Typing defaults types name p rest input bindings) :
    p.names ++ rest.names = bindings.map Prod.fst := by
  cases typed with
  | field below optional first last => simp only [List.map_append, ← first.binding_names, ← last.binding_names]

theorem typing_iff (bindings : NamedTypes) : Typing defaults types name p rest input bindings ↔
    ∃ original payload left right, bindings = left ++ right ∧ Common.Subtype input original ∧
      OptionalPayload name original payload ∧ RawTyping defaults types p payload left ∧
        RawTyping defaults (left ++ types) rest original right := by
  constructor
  · intro typed
    cases typed with
    | field below optional first last => exact ⟨_, _, _, _, rfl, below, optional, first, last⟩
  · rintro ⟨_, _, _, _, rfl, below, optional, first, last⟩
    exact .field below optional first last

def generate (name : Nat) (p rest : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (prior : NamedTerms α) (input : TyTerm α) (bindings : NamedTerms α) : Formula α :=
  let left := renameBindings (fun x => some (some x)) (bindings.take p.names.length)
  let right := renameBindings (fun x => some (some x)) (bindings.drop p.names.length)
  let preceding := renameBindings (fun x => some (some x)) prior
  .existsSlot (.existsSlot (.and (.tyLe (input.rename fun x => some (some x)) fresh₀.ty)
    (.and (CommonPatternDefaults.optionalConstraints name fresh₀.ty fresh₁.ty)
      (.and (CommonAlignedPatternGeneration.generatePattern p (env₂ environment) preceding fresh₁.ty left)
        (CommonAlignedPatternGeneration.generatePattern rest (env₂ environment) (left ++ preceding) fresh₀.ty right)))))

/-- Any prescribed shared binding references, defaults, captured instances
and input assignment. Optional payload constraints replace only the local
required-field demand; output order and the cumulative right scope agree. -/
theorem generate_exact (name : Nat) (p rest : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α) (semantic : List (Binding Common.model))
    (outer : EnvRel Common.model ρ symbolic semantic) (prior : NamedTerms α)
    (input : TyTerm α) (bindings : NamedTerms α) :
    (generate name p rest symbolic prior input bindings).Holds Common.model ρ ↔
      Typing (CommonPatternGeneration.DefaultTyping semantic) (evalTypes ρ prior) name p rest
        (input.eval Common.model ρ) (evalTypes ρ bindings) := by
  have children (a b : Comp Common.model) := CommonAlignedPatternGeneration.generatePattern_exact p
    (extend (extend ρ a) b) (env₂ symbolic) semantic ((outer.lift a).lift b)
  have tail (a b : Comp Common.model) := CommonAlignedPatternGeneration.generatePattern_exact rest
    (extend (extend ρ a) b) (env₂ symbolic) semantic ((outer.lift a).lift b)
  simp only [generate, Formula.Holds, children, tail, CommonPatternDefaults.optional_constraints_exact,
    evalTypes_rename, evalTypes_append, Function.comp_def, extend_some, fresh₀, fresh₁, CompTerm.var,
    TyTerm.eval_rename, TyTerm.eval]
  rw [typing_iff]
  constructor
  · rintro ⟨a, b, below, optional, first, last⟩
    refine ⟨a.1, b.1, _, _, ?_, below, optional, first, last⟩
    simp [evalTypes_take, evalTypes_drop]
  · rintro ⟨original, payload, left, right, output, below, optional, first, last⟩
    have length : p.names.length = left.length := by simpa using congrArg List.length first.binding_names
    have leftEq : evalTypes ρ (bindings.take p.names.length) = left := by simp [evalTypes_take, output, length]
    have rightEq : evalTypes ρ (bindings.drop p.names.length) = right := by simp [evalTypes_drop, output, length]
    exact ⟨(original, Common.rowEmpty), (payload, Common.rowEmpty), below, optional,
      by simpa only [leftEq, extend_none] using first, by simpa only [leftEq, rightEq, extend_none] using last⟩

open CommonPatternGenerationProvenance

theorem safe_generate (name : Nat) (p rest : Pattern Empty Inference.Expr)
    (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (prior : NamedTerms α) (priorGood : GoodBindings prior) (input : TyTerm α) (inputGood : Input input)
    (bindings : NamedTerms α) (bindingsGood : GoodBindings bindings) :
    SafeFormula (generate name p rest environment prior input bindings) := by
  let rename : α → Option (Option α) := fun x => some (some x)
  have left := bindings_rename (bindings_take bindingsGood p.names.length) rename
  have right := bindings_rename (bindings_drop bindingsGood p.names.length) rename
  have preceding := bindings_rename priorGood rename
  exact .existsSlot (.existsSlot (.and
    (safe_tyLe _ _ (inputGood.rename rename) (.old rfl) rfl)
    (.and (safe_optional name fresh₀.ty fresh₁.ty ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩)
      (.and (CommonAlignedPatternGenerationProvenance.safe_generatePattern p _ environmentGood.lift.lift
        _ preceding _ ⟨rfl, rfl, rfl⟩ _ left)
        (CommonAlignedPatternGenerationProvenance.safe_generatePattern rest _ environmentGood.lift.lift
          _ (bindings_append left preceding) _ ⟨rfl, rfl, rfl⟩ _ right)))))

end Yulang.CommonOptionalField
