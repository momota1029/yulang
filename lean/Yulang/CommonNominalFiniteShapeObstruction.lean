import Yulang.CommonNominalCoreCastRegistry
import Yulang.CoreResolved

/-!
# A pure Common source body outside all finite operational shapes

The actual lambda x. x x has a pure Common typing using a one-state regular
arrow type. No annotated OperationalTyping.Expr at any finite shape erases to
this source. This disproves a universal source-to-existing-shape bridge; it
does not disprove a future Common evaluator or the original B5 cast theorem.
-/

namespace Yulang.CommonNominalFiniteShapeObstruction

open CommonNominalCarrier
open Core.PresenceGeneration (Comp Binding)

def delta : Inference.Expr := .lam (.app (.var 0) (.var 0))

def coreDelta (signature : Core.Signature) : Core.Expr signature := .lam (.app (.var 0) (.var 0))

def body : CommonNominalGuardedClosure.Body 1 1 :=
  fun _ => .arrow (.inl 0) Common.rowEmpty (.inr 0) Common.rowEmpty

def recursiveType (result : Ty) : Ty := CommonNominalGuardedClosure.instantiate body (fun _ => result) 0

theorem recursive_unfold (result : Ty) :
    Equivalent (recursiveType result) (arrow (recursiveType result) Common.rowEmpty result Common.rowEmpty) :=
  CommonNominalGuardedClosure.all_parameter_sound body (fun _ => result) 0

theorem delta_typed (environment : List (Binding model)) (result : Ty) :
    Core.PresenceGeneration.Typing model environment delta
      (Core.PresenceGeneration.Comp.pure model (recursiveType result)) := by
  have input : Core.PresenceGeneration.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model (recursiveType result)) :: environment)
      (.var 0) (Core.PresenceGeneration.Comp.pure model (recursiveType result)) :=
    .var rfl (.mono ⟨subtype_refl _, Common.rowLe_refl _⟩)
  have function : Core.PresenceGeneration.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model (recursiveType result)) :: environment)
      (.var 0) (Core.PresenceGeneration.Comp.pure model
        (arrow (recursiveType result) Common.rowEmpty result Common.rowEmpty)) :=
    .var rfl (.mono ⟨(recursive_unfold result).1, Common.rowLe_refl _⟩)
  have applied : Core.PresenceGeneration.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model (recursiveType result)) :: environment)
      (.app (.var 0) (.var 0)) (Core.PresenceGeneration.Comp.pure model result) := by
    apply Core.PresenceGeneration.Typing.app
      (a := Core.PresenceGeneration.Comp.pure model (recursiveType result))
      (b := Core.PresenceGeneration.Comp.pure model result) (ef := Common.rowEmpty) function input
    exact ⟨subtype_refl _, fun _ present => present.elim id id⟩
  exact .lam applied ⟨(recursive_unfold result).2, Common.rowLe_refl _⟩

theorem delta_core_typed (result : Ty) : Core.CommonSyntax.Typing model [] (coreDelta Core.Signature.empty)
    (Core.PresenceGeneration.Comp.pure model (recursiveType result)) :=
  (Core.CommonSyntax.nominal_lowering_exact _ rfl (Core.CommonSyntax.EnvRel.nil model) _).mpr (delta_typed [] result)

def registry : CommonNominalCoreCastRegistry.Registry 2 (Fin 2) where
  endpoint := fun index => .var index
  adjacency := fun index => if index = 0 then [1] else []
  body := fun _ _ => coreDelta Core.Signature.empty

def assignment (result : Ty) (index : Fin 2) : Comp model :=
  if index = 0 then (.base .unit, Common.rowEmpty) else (recursiveType result, Common.rowEmpty)

/-- A concrete finite source registry with a base source, regular target and
the original pure lambda body. Validity comes from actual Common source typing. -/
theorem registry_valid (result : Ty) : registry.Valid [] (assignment result) := by
  intro first last edge
  by_cases atZero : first = 0
  · have lastOne : last = 1 := by simpa [registry, atZero] using edge
    subst first; subst last
    have bodyTyped := delta_typed
      [Binding.mono (Core.PresenceGeneration.Comp.pure model (.base .unit))] result
    have actual := (Core.CommonSyntax.nominal_lowering_exact (coreDelta Core.Signature.empty) rfl
      ((Core.CommonSyntax.EnvRel.nil model).mono (Core.PresenceGeneration.Comp.pure model (.base .unit)))
      (Core.PresenceGeneration.Comp.pure model (recursiveType result))).mpr bodyTyped
    simpa [registry, Core.PresenceGeneration.TyTerm.eval, assignment] using actual
  · simp [registry, atZero] at edge

theorem registry_generated_models (result : Ty) :
    (registry.generate []).Models (assignment result) :=
  (registry.generate_exact [] [] [] (assignment result) (Core.CommonSyntax.EnvRel.nil model)
    (Core.PresenceGeneration.EnvRel.nil model (assignment result))).mpr (registry_valid result)

private theorem var_lookup (index : OperationalTyping.Var context shape) :
    context[Core.Resolved.varIndex index]? = some shape := by
  induction index with
  | here => rfl
  | there index ih => exact ih

private theorem operational_var {scopes : Nat} {Key Atom : Type} {context : List OperationalTyping.Shape}
    {shape : OperationalTyping.Shape} (expression : OperationalTyping.Expr scopes Key Atom context shape)
    (same : Core.Resolved.operational expression = .var index) : context[index]? = some shape := by
  induction expression with
  | var slotIndex =>
      have equal : Core.Resolved.varIndex slotIndex = index := by simpa [Core.Resolved.operational] using same
      rw [← equal]
      exact var_lookup slotIndex
  | widen _ _ ih => exact ih same
  | _ => simp [Core.Resolved.operational] at same

private theorem operational_app {scopes : Nat} {Key Atom : Type} {context : List OperationalTyping.Shape}
    {shape : OperationalTyping.Shape} (expression : OperationalTyping.Expr scopes Key Atom context shape)
    (first last : Core.Resolved.Term scopes Key Atom)
    (same : Core.Resolved.operational expression = .app first last) :
    ∃ input, ∃ function : OperationalTyping.Expr scopes Key Atom context (.arrow input shape),
      ∃ argument : OperationalTyping.Expr scopes Key Atom context input,
        Core.Resolved.operational function = first ∧ Core.Resolved.operational argument = last := by
  induction expression with
  | app function argument _ _ =>
      have equal : Core.Resolved.operational function = first ∧ Core.Resolved.operational argument = last := by
        simpa [Core.Resolved.operational] using same
      exact ⟨_, function, argument, equal⟩
  | widen _ _ ih => exact ih same
  | _ => simp [Core.Resolved.operational] at same

private theorem operational_lam {scopes : Nat} {Key Atom : Type} {context : List OperationalTyping.Shape}
    {shape : OperationalTyping.Shape} (expression : OperationalTyping.Expr scopes Key Atom context shape)
    (source : Core.Resolved.Term scopes Key Atom)
    (same : Core.Resolved.operational expression = .lam source) :
    ∃ input output, ∃ body : OperationalTyping.Expr scopes Key Atom (input :: context) output,
      shape = .arrow input output ∧ Core.Resolved.operational body = source := by
  induction expression with
  | lam _ body _ =>
      have equal : Core.Resolved.operational body = source := by simpa [Core.Resolved.operational] using same
      exact ⟨_, _, body, rfl, equal⟩
  | widen _ _ ih => exact ih same
  | _ => simp [Core.Resolved.operational] at same

theorem no_finite_operational_delta {scopes : Nat} {Key Atom : Type} (context : List OperationalTyping.Shape)
    (shape : OperationalTyping.Shape) (expression : OperationalTyping.Expr scopes Key Atom context shape) :
    Core.Resolved.operational expression ≠ coreDelta ⟨Key, Key, Fin scopes, Empty, Atom⟩ := by
  intro same
  obtain ⟨input, output, inner, _, bodySame⟩ := operational_lam expression _ same
  obtain ⟨argumentShape, function, argument, functionSame, argumentSame⟩ := operational_app inner _ _ bodySame
  have functionType := operational_var function functionSame
  have argumentType := operational_var argument argumentSame
  simp only [List.getElem?_cons_zero, Option.some.injEq] at functionType argumentType
  have infinite : argumentShape = .arrow argumentShape output := argumentType.symm.trans functionType
  have impossible := congrArg sizeOf infinite
  simp only [OperationalTyping.Shape.arrow.sizeOf_spec] at impossible
  omega

/-- Even a type-only global bridge cannot both preserve pure arrows and
respect the actual regular Common equivalence at finite operational shapes. -/
theorem no_equivalence_preserving_arrow_shapes :
    ¬ ∃ erase : Ty → OperationalTyping.Shape,
      (∀ first last, erase (arrow first Common.rowEmpty last Common.rowEmpty) = .arrow (erase first) (erase last)) ∧
      (∀ first last, Equivalent first last → erase first = erase last) := by
  rintro ⟨erase, arrows, equivalents⟩
  let result : Ty := .base .unit
  have unfoldShape := equivalents _ _ (recursive_unfold result)
  rw [arrows] at unfoldShape
  have impossible := congrArg sizeOf unfoldShape
  simp only [OperationalTyping.Shape.arrow.sizeOf_spec] at impossible
  omega

end Yulang.CommonNominalFiniteShapeObstruction
