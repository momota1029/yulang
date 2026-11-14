import Yulang.GeneralNominalCenteredHeadMatPatternSemantics
import Yulang.GeneralNominalCenteredHeadMatStepChildReadback

set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCenteredHeadMatCompilerSemantics
open GeneralDeclarationPatterns GeneralCandidateInspection CommonNominalFullCarrier
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalMatchedAssembly (Aligned)
open GeneralNominalCenteredHeadMatExpressions (Expr primitiveValue value values)

private theorem aligned_length (same : Aligned relation first last) : first.length = last.length := by
  induction same with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

private theorem aligned_get {index : Nat} (same : Aligned relation first last)
    (one : first[index]? = some a) (two : last[index]? = some b) : relation a b := by
  induction same generalizing index with
  | nil => cases one
  | cons related _ ih =>
      cases index with
      | zero => cases Option.some.inj one; cases Option.some.inj two; exact related
      | succ index => exact ih one two

private theorem aligned_symm (same : Aligned Equivalent first last) : Aligned Equivalent last first := by
  induction same with
  | nil => exact .nil
  | cons pair _ ih => exact .cons (eqv_symm pair) ih

theorem nominal_congr (name : Nat) (same : Aligned Equivalent first last) :
    Equivalent (nominal name (first.map Sum.inl)) (nominal name (last.map Sum.inl)) := by
  have forward : ∀ {first last}, Aligned Equivalent first last →
      Subtype (nominal name (first.map Sum.inl)) (nominal name (last.map Sum.inl)) := by
    intro first last same
    apply (nominal_regular_invariant_exact ..).mpr
    refine ⟨rfl,by simp only [List.length_map]; exact aligned_length same,?_⟩
    intro index a b one two
    obtain ⟨x,hx,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using one)
    obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp (by simpa only [List.getElem?_map] using two)
    change Equivalent x y
    exact aligned_get same hx hy
  exact ⟨forward same,forward (aligned_symm same)⟩

theorem primitive_congr (constructor : Primitive) (same : Aligned Equivalent first last) :
    Equivalent (primitiveValue constructor first) (primitiveValue constructor last) := by
  cases constructor with
  | scalar | emptyRecord | exactEmpty =>
      cases same <;> exact eqv_refl _
  | pair =>
      cases same with
      | nil => exact eqv_refl _
      | cons first rest =>
          cases rest with
          | nil => exact eqv_refl _
          | cons last remaining =>
              cases remaining with
              | nil => exact ⟨(common_pair_iff ..).mpr ⟨first.1,last.1⟩,
                  (common_pair_iff ..).mpr ⟨first.2,last.2⟩⟩
              | cons => exact eqv_refl _

def application (catalogue : Constructors) (interpretation : GeneralNominalInspection.Interpretation)
    (name : Nat) (arguments : List Ty) : Ty :=
  match interpretation.primitives name with
  | some primitive => primitiveValue primitive arguments
  | none => match catalogue name with
    | some declaration => nominal declaration.name (arguments.map Sum.inl)
    | none => .bottom

def algebra (catalogue : Constructors) (interpretation : GeneralNominalInspection.Interpretation) : Algebra where
  application := application catalogue interpretation
  congruent := by
    intro name first last same
    unfold application
    split
    · exact primitive_congr _ same
    · split
      · exact nominal_congr _ same
      · exact eqv_refl _

theorem application_value
    (compiled : GeneralNominalCenteredHeadMatExpressions.application catalogue interpretation name arguments = some expression) :
    value variables .actual expression = application catalogue interpretation name (values variables .actual arguments) := by
  cases declared : catalogue name with
  | none => simp [GeneralNominalCenteredHeadMatExpressions.application,declared] at compiled
  | some declaration =>
      by_cases arity : declaration.parameters.length = arguments.length
      · simp [GeneralNominalCenteredHeadMatExpressions.application,declared,arity] at compiled
        cases primitive : interpretation.primitives name with
        | none =>
            simp only [primitive] at compiled
            split at compiled
            · cases Option.some.inj compiled
              simp only [value,application,primitive,declared]
            · cases compiled
        | some primitiveValue =>
            simp only [primitive] at compiled
            split at compiled
            · cases Option.some.inj compiled
              simp only [value,application,primitive]
            · cases compiled
      · simp [GeneralNominalCenteredHeadMatExpressions.application,declared,arity] at compiled

mutual
  theorem translate_value (pattern : Pattern)
      (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression) :
      value variables .actual expression = eval (algebra catalogue interpretation) (variables .actual) pattern := by
    cases pattern with
    | var name => cases Option.some.inj compiled; rfl
    | app name arguments =>
        cases translated : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation arguments <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,translated,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · rw [application_value compiled,translate_values arguments translated]
          rfl
    | record label payload tail =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation payload <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,one,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · cases two : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation tail <;>
            simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
          · cases compiled
          · cases Option.some.inj compiled
            simp only [value,eval,translate_value payload one,translate_value tail two]
    | variant tag payload =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation payload <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,one,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
        · cases compiled
        · cases Option.some.inj compiled
          simp only [value,eval,translate_value payload one]
    | join first last =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation first <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,one,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · cases two : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation last <;>
            simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
          · cases compiled
          · cases Option.some.inj compiled
            simp only [value,eval,translate_value first one,translate_value last two]
    termination_by sizeOf pattern
  theorem translate_values (patterns : List Pattern)
      (compiled : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation patterns = some expressions) :
      values variables .actual expressions = evals (algebra catalogue interpretation) (variables .actual) patterns := by
    cases patterns with
    | nil => cases Option.some.inj compiled; rfl
    | cons head tail =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation head <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translateMany,one,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · cases two : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation tail <;>
            simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
          · cases compiled
          · cases Option.some.inj compiled
            simp only [values,evals,translate_value head one,translate_values tail two]
    termination_by sizeOf patterns
end

theorem compiled_normalized
    (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression) :
    Equivalent (value variables .actual expression)
      (eval (algebra catalogue interpretation) (variables .actual) (normalize pattern)) := by
  rw [translate_value pattern compiled]
  exact normalize_sound pattern

variable {roles : Roles.RoleDecls} {plan : GeneralNominalCenters.Plan roles}
  {model : GeneralNominalCommonBridge.Assignment}

theorem child_normalized (branch : GeneralNominalCenteredHeadMatStepPackets.Holds plan model)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : GeneralDeclarations.Clause.Signature roles clause)
    (index : Fin (roles clause.role).arity)
    (covered : GeneralNominalCenteredHeadWFSource.PatternCovered plan.packet.registry.constructors plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))) :
    Equivalent (model ((plan.childSite clause signature).center index)).1
      (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
        (fun name => (model (plan.binder name)).1)
        (normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)))) := by
  obtain ⟨expression,translated⟩ := GeneralNominalCenteredHeadMatExpressions.translate_complete covered
  have actual := GeneralNominalCenteredHeadMatStepChildReadback.argument_value branch member signature index translated
  have normalized := compiled_normalized (variables := GeneralNominalCenteredHeadMatEffects.variables plan model) translated
  have variables : GeneralNominalCenteredHeadMatEffects.variables plan model .actual = fun name => (model (plan.binder name)).1 := by
    funext name
    simp only [GeneralNominalCenteredHeadMatEffects.variables,ite_self]
  rw [variables] at normalized
  exact eqv_trans actual normalized

end Yulang.GeneralNominalCenteredHeadMatCompilerSemantics
