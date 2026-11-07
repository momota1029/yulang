import Yulang.CommonNominalFullModelMap
import Yulang.CoreCommonInference

/-!
# Old presence typing and actual solved schemes in the nominal carrier

Every old computation and captured binding is transported, including prescribed
polymorphic signatures. Their type parameters use a total syntactic retraction
which is a left inverse on embedded old types. It imposes no condition on a
scheme parameter. The original inference computation and list remain unchanged.
-/

namespace Yulang.CommonNominalFullTypingPreservation

open Core.PresenceGeneration
open CommonNominalFullCarrier
open CommonNominalFullModelMap (value retract retract_value)

abbrev comp (original : Comp Common.model) : Comp model := (value original.1, original.2)

theorem comp_le_exact (first last : Comp Common.model) :
    Comp.le model (comp first) (comp last) ↔ Comp.le Common.model first last :=
  and_congr (CommonNominalFullModelMap.subtype_exact first.1 last.1) Iff.rfl

theorem comp_le {first last : Comp Common.model} (bounded : Comp.le Common.model first last) :
    Comp.le model (comp first) (comp last) := (comp_le_exact first last).mpr bounded

def binding : Binding Common.model → Binding model
  | .mono original => .mono (comp original)
  | .poly expression captured => .poly expression (captured.map binding)
  | .signature count instantiate => .signature count
      (fun parameters => comp (instantiate (fun index => retract (parameters index))))

/-- All old environments, expressions and result computations, including
captured polymorphic environments, exact/default records and prescribed
signatures. No syntax-support, fuel or successful-inference premise. -/
theorem typing_preserved {environment : List (Binding Common.model)}
    {expression : Inference.Expr} {result : Comp Common.model}
    (typed : Typing Common.model environment expression result) :
    Typing model (environment.map binding) expression (comp result) := by
  induction typed using Typing.rec
    (motive_2 := fun b c _ => BindingTyping model (binding b) (comp c))
  all_goals try simp only [binding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  case app =>
    rename_i Γ f a b ef x c typedF typedX bounded ihf iha
    exact .app (a := comp a) (b := comp b) ihf iha (comp_le bounded)
  case signature =>
    rename_i result count instantiate parameters bounded
    apply BindingTyping.signature (ι := fun index => value (parameters index))
    have same : (fun index => retract (value (parameters index))) = parameters := by
      funext index
      exact retract_value _
    simpa only [same] using comp_le bounded
  all_goals first
    | apply Typing.letValue <;> assumption
    | apply Typing.lit; exact comp_le ‹_›
    | apply Typing.lam <;> first | assumption | exact comp_le ‹_›
    | apply Typing.app <;> first | assumption | exact comp_le ‹_›
    | apply Typing.letComputed <;> first | assumption | exact comp_le ‹_›
    | apply Typing.branch <;> first | assumption | exact comp_le ‹_›
    | apply Typing.pair <;> first | assumption | exact comp_le ‹_›
    | apply Typing.fst <;> first | assumption | exact comp_le ‹_›
    | apply Typing.snd <;> first | assumption | exact comp_le ‹_›
    | apply Typing.emptyRecord; exact comp_le ‹_›
    | apply Typing.record <;> first
        | assumption
        | exact comp_le ‹_›
        | exact (CommonNominalFullModelMap.subtype_exact _ _).mpr ‹_›
    | apply Typing.recordDefault <;> first
        | assumption
        | exact comp_le ‹_›
        | exact (CommonNominalFullModelMap.subtype_exact _ _).mpr ‹_›
    | apply Typing.field <;> first | assumption | exact comp_le ‹_›
    | apply Typing.variant <;> first | assumption | exact comp_le ‹_›
    | apply BindingTyping.mono; exact comp_le ‹_›
    | apply BindingTyping.poly <;> assumption

private theorem data_typing_preserved {value : Core.CommonData.Value} {result : Comp Common.model}
    (typed : Core.CommonData.ValueTyping Common.model value result) :
    Core.CommonData.ValueTyping model value (comp result) := by
  induction typed with
  | literal bounded => exact .literal (comp_le bounded)
  | pair _ _ bounded first last => exact .pair first last (comp_le bounded)
  | emptyRecord bounded => exact .emptyRecord (comp_le bounded)
  | record _ _ recordType bounded head rest =>
      exact .record head rest ((CommonNominalFullModelMap.subtype_exact _ _).mpr recordType) (comp_le bounded)
  | variant _ bounded payload => exact .variant payload (comp_le bounded)

def coreBinding : Core.CommonSyntax.Binding Common.model → Core.CommonSyntax.Binding model
  | .mono original => .mono (comp original)
  | .poly expression captured => .poly expression (captured.map coreBinding)
  | .signature count instantiate => .signature count
      (fun parameters => comp (instantiate (fun index => retract (parameters index))))

/-- All old Common source environments and source syntax, retaining original
literal contents, structural data, strict application and name cases. -/
theorem core_typing_preserved_in_environment
    {environment : List (Core.CommonSyntax.Binding Common.model)}
    {expression : Core.Required.Term} {result : Comp Common.model}
    (typed : Core.CommonSyntax.Typing Common.model environment expression result) :
    Core.CommonSyntax.Typing model (environment.map coreBinding) expression (comp result) := by
  induction typed using Core.CommonSyntax.Typing.rec
    (motive_2 := fun b c _ => Core.CommonSyntax.BindingTyping model (coreBinding b) (comp c))
  all_goals try simp only [coreBinding, List.map_cons] at *
  case var found _ ih => exact .var (by simp [List.getElem?_map, found]) ih
  case app =>
    rename_i Γ f a b ef x c typedF typedX bounded ihf iha
    exact .app (a := comp a) (b := comp b) ihf iha (comp_le bounded)
  case signature =>
    rename_i result count instantiate parameters bounded
    apply Core.CommonSyntax.BindingTyping.signature (ι := fun index => value (parameters index))
    have same : (fun index => retract (value (parameters index))) = parameters := by
      funext index
      exact retract_value _
    simpa only [same] using comp_le bounded
  case data typed => exact .data (data_typing_preserved typed)
  case strictApp =>
    rename_i Γ f a b ef x actual c typedF typedX compatible bounded ihf iha
    exact .strictApp (a := comp a) (b := comp b) (actual := comp actual)
      ihf iha (comp_le compatible) (comp_le bounded)
  all_goals first
    | apply Core.CommonSyntax.Typing.letValue <;> assumption
    | apply Core.CommonSyntax.Typing.lit; exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.literal; exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.lam <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.strictApp <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.letComputed <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.leaf; assumption
    | apply Core.CommonSyntax.Typing.caseName <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.branch <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.pair <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.fst <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.snd <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.emptyRecord; exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.record <;> first
        | assumption
        | exact comp_le ‹_›
        | exact (CommonNominalFullModelMap.subtype_exact _ _).mpr ‹_›
    | apply Core.CommonSyntax.Typing.recordDefault <;> first
        | assumption
        | exact comp_le ‹_›
        | exact (CommonNominalFullModelMap.subtype_exact _ _).mpr ‹_›
    | apply Core.CommonSyntax.Typing.field <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.Typing.variant <;> first | assumption | exact comp_le ‹_›
    | apply Core.CommonSyntax.BindingTyping.mono; exact comp_le ‹_›
    | apply Core.CommonSyntax.BindingTyping.poly <;> assumption

theorem core_typing_preserved (expression : Core.Required.Term) (result : Comp Common.model)
    (typed : Core.Typing (Core.CommonSyntax.model Common.model) [] expression result) :
    Core.Typing (Core.CommonSyntax.model model) [] expression (comp result) :=
  core_typing_preserved_in_environment typed

/-- Every actual old returned scheme, with every one of its original arbitrary
parameters. The scheme and its parameter product are not filtered or changed. -/
theorem old_solver_all_parameters (expression : Core.Required.Term)
    (scheme : CommonSolvedSource.Scheme) (returned : scheme ∈ Core.infer expression)
    (parameters : scheme.Parameters) :
    Core.Typing (Core.CommonSyntax.model model) [] expression (comp (scheme.instantiate parameters)) :=
  core_typing_preserved expression _ (Core.infer_instantiates expression scheme returned parameters)

/-- The original finite solved list has exactly its original instances on
embedded old targets, in the new carrier's actual subtype order. This is an
old-solver preservation theorem, not a solver for new construction problems. -/
theorem old_solver_instances_exact (expression : Core.Required.Term) (result : Comp Common.model) :
    (∃ scheme ∈ Core.infer expression, ∃ parameters : scheme.Parameters,
      Comp.le model (comp (scheme.instantiate parameters)) (comp result)) ↔
    Core.Typing (Core.CommonSyntax.model Common.model) [] expression result := by
  simp only [comp_le_exact]
  exact (Core.infer_principal expression result).symm

end Yulang.CommonNominalFullTypingPreservation
