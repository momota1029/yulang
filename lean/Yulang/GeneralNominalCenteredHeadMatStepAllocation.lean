import Yulang.GeneralNominalCenteredHeadMatExtension

/-! A simultaneous assignment permits repeated targets when their values
agree. References to a target are safe when that assignment preserves the
referenced value. This includes emitted variable identities such as x = x. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepAllocation
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCenteredHeadMatExtension
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalMaterialization (Mode)
variable {schema : Schema} {journal : Assignment → Prop}

def Coherent (resolve : Mode → Nat → Nat) (before : Assignment) (equations : List Equation) : Prop :=
  ∀ first ∈ equations, ∀ last ∈ equations, first.target = last.target →
    value (sources resolve before) first.mode first.expression =
      value (sources resolve before) last.mode last.expression

def StableReferences (resolve : Mode → Nat → Nat) (before : Assignment) (equations : List Equation) : Prop :=
  ∀ equation ∈ equations, ∀ mode name, name ∈ names equation.expression →
    ∀ assigned ∈ equations, assigned.target = resolve mode name →
      value (sources resolve before) assigned.mode assigned.expression = (before (resolve mode name)).1

theorem extend_preserves
    (kept : ∀ equation ∈ equations, equation.target = identity →
      value (sources resolve before) equation.mode equation.expression = (before identity).1) :
    extend resolve before equations identity = before identity := by
  unfold extend
  split
  · rfl
  · rename_i equation found
    rw [kept equation (List.mem_of_find?_eq_some found) (by simpa using List.find?_some found)]

theorem coherent_target (coherent : Coherent resolve before equations) (member : equation ∈ equations) :
    extend resolve before equations equation.target =
      (value (sources resolve before) equation.mode equation.expression,(before equation.target).2) := by
  have existsTarget : ∃ found, equations.find? (fun other => other.target == equation.target) = some found := by
    cases located : equations.find? (fun other => other.target == equation.target) with
    | none =>
        have absent := List.find?_eq_none.mp located equation member
        simp at absent
    | some found => exact ⟨found,rfl⟩
  obtain ⟨found,present⟩ := existsTarget
  have equal := coherent found (List.mem_of_find?_eq_some present) equation member
    (by simpa using List.find?_some present)
  simp only [extend,present,equal]
  rfl

theorem independent_stable (independent : Independent resolve equations) : StableReferences resolve before equations := by
  intro equation member mode name used assigned present equal
  exact False.elim (independent equation member mode name used (List.mem_map.mpr ⟨assigned,present,equal⟩))

theorem schema_extension (coherent : Coherent resolve before schema.equations)
    (stable : StableReferences resolve before schema.equations) :
    schema.Holds (sources resolve (extend resolve before schema.equations))
      (extend resolve before schema.equations) := by
  intro equation member
  have rhs : value (sources resolve (extend resolve before schema.equations)) equation.mode equation.expression =
      value (sources resolve before) equation.mode equation.expression := by
    apply value_congr
    intro mode name used
    unfold sources
    rw [extend_preserves (stable equation member mode name used)]
  unfold Equation.Holds
  rw [rhs,coherent_target coherent member]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem common_model_extension (valid : journal before)
    (coherent : Coherent resolve before schema.equations)
    (stable : StableReferences resolve before schema.equations)
    (preserved : ∀ after : Assignment,
      (∀ identity, identity ∉ schema.equations.map Equation.target → after identity = before identity) →
      journal before → journal after) :
    ∃ after, journal after ∧ schema.Holds (sources resolve after) after ∧
      ∀ identity, identity ∉ schema.equations.map Equation.target → after identity = before identity := by
  exact ⟨extend resolve before schema.equations,preserved _ (fun _ outside => extend_outside outside) valid,schema_extension coherent stable,
    fun _ outside => extend_outside outside⟩

theorem variable_identity (resolve : Mode → Nat → Nat) (before : Assignment) (mode : Mode) (name : Nat) :
    let equation : Equation := ⟨resolve mode name,mode,.variable name⟩
    Coherent resolve before [equation] ∧ StableReferences resolve before [equation] ∧
      extend resolve before [equation] = before := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro first one last two _
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    rfl
  · intro equation member other name' _ assigned present equal
    cases List.mem_singleton.mp member
    cases List.mem_singleton.mp present
    change (before (resolve mode name)).1 = _
    exact congrArg (fun identity => (before identity).1) equal
  · funext identity
    apply extend_preserves
    intro equation member equal
    cases List.mem_singleton.mp member
    change (before (resolve mode name)).1 = _
    exact congrArg (fun identity => (before identity).1) equal

end Yulang.GeneralNominalCenteredHeadMatStepAllocation
