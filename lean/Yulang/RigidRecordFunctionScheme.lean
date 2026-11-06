import Yulang.RigidRecordValueInference

/-!
# A free-parameter scheme for extending an unknown input record

The original core expression is `lam (record label (lit base) (var 0))`.
Its descriptor compiles to a finite type term with three free value parameters
and one free row. For parameters `alpha`, `beta`, `gamma`, and `rho`, put

* `I = alpha & {}`,
* `H = base | beta`,
* `T = (I | gamma) & {}`.

The resulting function is `(I ! rho) -> (record label H T ! rho)`, with empty
outer row. Every parameter tuple is valid. Conversely, an arbitrary original
typing recovers its input row and both widened construction slots from these
parameters. Record congruence, not covariance toward an opaque tail, provides
the retraction.

This is a principal scheme for one open-tail function family, not a new
ad-hoc source inference dispatcher or a claim about the whole source core.
-/

namespace Yulang.RigidRecordFunctionScheme

open Inference
open StructuralBase (Ty)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordValueInference (model clamp_lower clamp_retract widen_retract)

universe u

variable {Row : Type u}

def source (label : Nat) (base : Base) : Expr :=
  .lam (.record label (.lit base) (.var 0))

/-- The syntax is computed from the field label and literal base. Slots zero,
one and two contribute value types; slot three contributes only its row. -/
def scheme (label : Nat) (base : Base) : CompTerm (Fin 4) :=
  let input : TyTerm (Fin 4) := .inter (.var 0) .emptyRecord
  let head : TyTerm (Fin 4) := .union (.base base) (.var 1)
  let tail : TyTerm (Fin 4) := .inter (.union input (.var 2)) .emptyRecord
  .pure (.arrow input (.var 3) (.record label head tail) (.var 3))

structure Parameters (m : Model) where
  argument : m.Ty
  headUpper : m.Ty
  tailUpper : m.Ty
  row : m.Row

def Parameters.assignment (m : Model) (parameter : Parameters m) : Fin 4 → Comp m :=
  fun index => match index.val with
    | 0 => (parameter.argument, m.empty)
    | 1 => (parameter.headUpper, m.empty)
    | 2 => (parameter.tailUpper, m.empty)
    | _ => (m.bottom, parameter.row)

def inputType (m : Model) (parameter : Parameters m) : m.Ty :=
  m.inter parameter.argument m.emptyRecord

def headType (m : Model) (base : Base) (parameter : Parameters m) : m.Ty :=
  m.union (m.base base) parameter.headUpper

def tailType (m : Model) (parameter : Parameters m) : m.Ty :=
  m.inter (m.union (inputType m parameter) parameter.tailUpper) m.emptyRecord

def instantiate (m : Model) (label : Nat) (base : Base) (parameter : Parameters m) : Comp m :=
  (m.arrow (inputType m parameter) parameter.row
    (m.record label (headType m base parameter) (tailType m parameter)) parameter.row, m.empty)

theorem instantiate_eq_eval (m : Model) (label : Nat) (base : Base) (parameter : Parameters m) :
    instantiate m label base parameter = (scheme label base).eval m (parameter.assignment m) := rfl

def Parameters.map (morphism : ModelMap sourceModel targetModel)
    (parameter : Parameters sourceModel) : Parameters targetModel :=
  ⟨morphism.value parameter.argument, morphism.value parameter.headUpper,
    morphism.value parameter.tailUpper, morphism.row parameter.row⟩

theorem Parameters.map_surjective (morphism : ModelMap sourceModel targetModel)
    (valueSurjective : ∀ target, ∃ source, morphism.value source = target)
    (rowSurjective : ∀ target, ∃ source, morphism.row source = target)
    (parameter : Parameters targetModel) :
    ∃ original : Parameters sourceModel, original.map morphism = parameter := by
  obtain ⟨argument, head, tail, row⟩ := parameter
  obtain ⟨input, inputEqual⟩ := valueSurjective argument
  obtain ⟨headValue, headEqual⟩ := valueSurjective head
  obtain ⟨tailValue, tailEqual⟩ := valueSurjective tail
  obtain ⟨rowValue, rowEqual⟩ := rowSurjective row
  exact ⟨⟨input, headValue, tailValue, rowValue⟩,
    by simp only [Parameters.map, inputEqual, headEqual, tailEqual, rowEqual]⟩

theorem instantiate_map (morphism : ModelMap sourceModel targetModel) (label : Nat) (base : Base)
    (parameter : Parameters sourceModel) :
    morphism.comp (instantiate sourceModel label base parameter) =
      instantiate targetModel label base (parameter.map morphism) := by
  simp only [ModelMap.comp, instantiate, inputType, headType, tailType, Parameters.map,
    morphism.arrow, morphism.record, morphism.inter, morphism.union, morphism.base,
    morphism.emptyRecord, morphism.empty]

def Instance (m : Model) (label : Nat) (base : Base) (target : Comp m) : Prop :=
  ∃ parameter : Parameters m, Comp.le m (instantiate m label base parameter) target

theorem input_retract {leRow : Row → Row → Prop} {input : Ty Row}
    (admissible : Subtype leRow input .emptyRecord) :
    Equivalent leRow (.inter input .emptyRecord) input :=
  ⟨.interLeft _ _, .interIntro (.refl _) admissible⟩

/-- All three value parameters and the row are entirely free. -/
theorem instantiate_sound (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (parameter : Parameters (model algebra)) :
    Typing (model algebra) [] (source label base) (instantiate (model algebra) label base parameter) := by
  apply Typing.lam
    (a := (inputType (model algebra) parameter, parameter.row))
    (b := ((model algebra).record label (headType (model algebra) base parameter)
      (tailType (model algebra) parameter), parameter.row))
  · apply Typing.record
      (a := (headType (model algebra) base parameter, algebra.empty))
      (b := (tailType (model algebra) parameter, parameter.row))
    · exact .lit ⟨.unionLeft _ _, algebra.refl _⟩
    · exact .var rfl (.mono ⟨clamp_lower (.interRight _ _) _, algebra.refl _⟩)
    · exact .interRight _ _
    · exact ⟨.refl _, (algebra.join_le_iff _ _ _).mpr ⟨algebra.empty_le _, algebra.refl _⟩⟩
  · exact ⟨.refl _, algebra.refl _⟩

/-- The source typing itself supplies the parameter tuple. Its widened head
and tail are retained; the input computation row is shared in both arrow
positions, with later output-row widening handled by ordinary subtyping. -/
theorem typing_complete (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) (typed : Typing (model algebra) [] (source label base) target) :
    Instance (model algebra) label base target := by
  cases typed with
  | lam bodyTyped outerBound =>
      rename_i input result
      cases bodyTyped with
      | record headTyped tailTyped admissible bodyBound =>
          rename_i head tail
          cases headTyped with
          | lit headBound =>
              cases tailTyped with
              | var found bindingTyped =>
                  cases found
                  cases bindingTyped with
                  | mono tailBound =>
                      let parameter : Parameters (model algebra) := ⟨input.1, head.1, tail.1, input.2⟩
                      have inputEqual := input_retract (.trans tailBound.1 admissible)
                      have headEqual := widen_retract headBound.1
                      have tailEqual := clamp_retract (.trans inputEqual.1 tailBound.1) admissible
                      have outputBelow := Subtype.trans
                        (RigidSemanticRecords.record_congr label headEqual tailEqual).1 bodyBound.1
                      have rowBelow := algebra.trans tailBound.2
                        ((algebra.join_le_iff _ _ _).mp bodyBound.2).2
                      exact ⟨parameter,
                        .trans (.arrow inputEqual.2 (algebra.refl _) outputBelow rowBelow) outerBound.1,
                        outerBound.2⟩

/-- Full principal instance equality for the original open-tail function
family. No success, typing, or parameter constraint is a premise. -/
theorem instances_exact (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    Instance (model algebra) label base target ↔ Typing (model algebra) [] (source label base) target := by
  constructor
  · rintro ⟨parameter, bounded⟩
    exact ConstraintProblems.typing_subsumption (model algebra) Subtype.trans algebra.refl
      (fun first last => algebra.trans first last) (instantiate_sound algebra label base parameter) bounded
  · exact typing_complete algebra label base target

theorem principal_formula_exact (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (target : Comp (model algebra)) :
    Instance (model algebra) label base target ↔
      (principal ([] : SchemeEnv Empty) (source label base)).Holds
        (model algebra) (extend Empty.elim target) :=
  (instances_exact algebra label base target).trans
    (principal_exact (model algebra) (source label base) [] [] Empty.elim
      (EnvRel.nil (model algebra) Empty.elim) target).symm

/-- In particular the scheme retains the same arbitrary admissible record
and the same arbitrary row on input and output, even when the record is not
equivalent to a rigid spine. -/
theorem diagonal_instance (algebra : RowFlowSchemes.Algebra Row) (label : Nat) (base : Base)
    (record : Ty Row) (row : Row) (admissible : Subtype algebra.le record .emptyRecord) :
    Instance (model algebra) label base
      (.arrow record row (.record label (.base base) record) row, algebra.empty) := by
  let parameter : Parameters (model algebra) := ⟨record, .base base, record, row⟩
  have inputEqual := input_retract admissible
  have resultEqual := RigidSemanticRecords.record_congr label (widen_retract (.refl (.base base)))
    (clamp_retract inputEqual.1 admissible)
  exact ⟨parameter, .arrow inputEqual.2 (algebra.refl _) resultEqual.1 (algebra.refl _), algebra.refl _⟩

end Yulang.RigidRecordFunctionScheme
