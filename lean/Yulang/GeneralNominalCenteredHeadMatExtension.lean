import Yulang.GeneralNominalCenteredHeadMatSchemas
import Yulang.GeneralNominalCenteredModelExtension

set_option backward.isDefEq.respectTransparency false

/-! A finite family of independently allocated output targets has an explicit
model extension. Preservation of an existing journal is kept separate from
syntactic materialization coverage. -/
namespace Yulang.GeneralNominalCenteredHeadMatExtension
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

mutual
  def names : Expr → List Nat
    | .variable name => [name]
    | .primitive _ arguments | .nominal _ arguments => namesMany arguments
    | .record _ payload tail | .join payload tail => names payload ++ names tail
    | .variant _ payload => names payload
  def namesMany : List Expr → List Nat
    | [] => []
    | first :: rest => names first ++ namesMany rest
end

private theorem congrArg2 (f : α → β → γ) (first : a = b) (last : c = d) : f a c = f b d := by
  cases first
  cases last
  rfl

mutual
  theorem value_congr (expression : Expr)
      (agree : ∀ mode name, name ∈ names expression → first mode name = last mode name) :
      value first mode expression = value last mode expression := by
    cases expression with
    | «variable» name => exact agree mode name (List.mem_singleton_self _)
    | primitive constructor arguments =>
        exact congrArg (primitiveValue constructor) (values_congr arguments agree)
    | nominal name arguments =>
        exact congrArg (fun arguments => nominal name (arguments.map Sum.inl)) (values_congr arguments agree)
    | record label payload tail =>
        exact congrArg2 (record label)
          (value_congr payload (fun m n h => agree m n (List.mem_append_left _ h)))
          (value_congr tail (fun m n h => agree m n (List.mem_append_right _ h)))
    | variant tag payload => exact congrArg (variant tag) (value_congr payload agree)
    | join a b =>
        exact congrArg2 CommonNominalSyntax.Layer.union
          (value_congr a (fun m n h => agree m n (List.mem_append_left _ h)))
          (value_congr b (fun m n h => agree m n (List.mem_append_right _ h)))
  theorem values_congr (expressions : List Expr)
      (agree : ∀ mode name, name ∈ namesMany expressions → first mode name = last mode name) :
      values first mode expressions = values last mode expressions := by
    cases expressions with
    | nil => rfl
    | cons head rest =>
        exact congrArg2 List.cons
          (value_congr head (fun m n h => agree m n (List.mem_append_left _ h)))
          (values_congr rest (fun m n h => agree m n (List.mem_append_right _ h)))
end

def sources (resolve : Mode → Nat → Nat) (model : Assignment) (mode : Mode) (name : Nat) : Ty :=
  (model (resolve mode name)).1

def extend (resolve : Mode → Nat → Nat) (before : Assignment) (equations : List Equation) : Assignment :=
  fun identity => match equations.find? (fun equation => equation.target == identity) with
    | none => before identity
    | some equation => (value (sources resolve before) equation.mode equation.expression,(before identity).2)

def Independent (resolve : Mode → Nat → Nat) (equations : List Equation) : Prop :=
  ∀ equation ∈ equations, ∀ mode name, name ∈ names equation.expression →
    resolve mode name ∉ equations.map Equation.target

variable {schema : Schema} {before : Assignment} {journal : Assignment → Prop}

theorem extend_outside (outside : identity ∉ equations.map Equation.target) :
    extend resolve before equations identity = before identity := by
  have absent : equations.find? (fun equation => equation.target == identity) = none := by
    apply List.find?_eq_none.mpr
    intro equation member
    intro equal
    exact outside (List.mem_map.mpr ⟨equation,member,of_decide_eq_true equal⟩)
  simp [extend,absent]

theorem extend_target (unique : (equations.map Equation.target).Nodup) (member : equation ∈ equations) :
    extend resolve before equations equation.target =
      (value (sources resolve before) equation.mode equation.expression,(before equation.target).2) := by
  have found : equations.find? (fun other => other.target == equation.target) = some equation := by
    induction equations with
    | nil => cases member
    | cons first rest ih =>
        have pair := List.nodup_cons.mp unique
        rcases List.mem_cons.mp member with equal | within
        · subst equation
          simp
        · have different : first.target ≠ equation.target :=
            fun equal => pair.1 (List.mem_map.mpr ⟨equation,within,equal.symm⟩)
          simpa only [List.find?,beq_eq_false_iff_ne.mpr different] using ih pair.2 within
  simp [extend,found]

theorem extend_holds (unique : (schema.equations.map Equation.target).Nodup)
    (independent : Independent resolve schema.equations) :
    schema.Holds (sources resolve (extend resolve before schema.equations))
      (extend resolve before schema.equations) := by
  intro equation member
  have rhs : value (sources resolve (extend resolve before schema.equations)) equation.mode equation.expression =
      value (sources resolve before) equation.mode equation.expression := by
    apply value_congr
    intro mode name used
    unfold sources
    rw [extend_outside (independent equation member mode name used)]
  unfold Equation.Holds
  rw [rhs,extend_target unique member]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem common_model_extension (valid : journal before)
    (unique : (schema.equations.map Equation.target).Nodup)
    (independent : Independent resolve schema.equations)
    (preserved : ∀ after : Assignment,
      (∀ identity, identity ∉ schema.equations.map Equation.target → after identity = before identity) → journal before → journal after) :
    ∃ after, journal after ∧ schema.Holds (sources resolve after) after ∧
      ∀ identity, identity ∉ schema.equations.map Equation.target → after identity = before identity := by
  have outside : ∀ identity, identity ∉ schema.equations.map Equation.target →
      extend resolve before schema.equations identity = before identity :=
    fun _ present => extend_outside present
  exact ⟨extend resolve before schema.equations,preserved _ outside valid,extend_holds unique independent,outside⟩

theorem source_model_extension (valid : GeneralNominalState.Models state before)
    (unique : (schema.equations.map Equation.target).Nodup)
    (independent : Independent resolve schema.equations)
    (fresh : ∀ equation ∈ schema.equations, equation.target ∉ GeneralNominalState.sources state) :
    ∃ after, GeneralNominalState.Models state after ∧ schema.Holds (sources resolve after) after ∧
      ∀ identity ∈ GeneralNominalState.sources state, after identity = before identity := by
  have outside (identity : Nat) (member : identity ∈ GeneralNominalState.sources state) :
      identity ∉ schema.equations.map Equation.target := by
    rintro present
    obtain ⟨equation,equationMember,rfl⟩ := List.mem_map.mp present
    exact fresh equation equationMember member
  refine ⟨extend resolve before schema.equations,?_,extend_holds unique independent,?_⟩
  · exact GeneralNominalCenteredModelExtension.source_models_same state
      (fun identity member => (extend_outside (outside identity member)).symm) valid
  · exact fun identity member => extend_outside (outside identity member)

end Yulang.GeneralNominalCenteredHeadMatExtension
