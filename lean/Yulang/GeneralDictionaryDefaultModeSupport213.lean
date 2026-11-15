import Yulang.GeneralDictionaryDefaultModeSupport212

/-! Mode-sensitive support for total expressions. Nominal arguments switch to
actual mode; no unused lower/upper captures are demanded for actual outputs. -/
namespace Yulang.GeneralDictionaryDefaultModeSupport213
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalMaterialization (Mode)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatExtension (sources)
open GeneralNominalCenteredFrame179 (Agree)
variable {first last : Assignment}

open GeneralDictionaryDefaultModeSupport212 (reads readMany value_same)

def schemaSources (resolve : Mode → Nat → Nat) (schema : Schema) : List Nat :=
  schema.equations.flatMap fun equation => equation.target :: reads resolve equation.mode equation.expression

theorem schema_iff (resolve : Mode → Nat → Nat) (schema : Schema)
    (same : Agree (schemaSources resolve schema) first last) :
    schema.Holds (sources resolve first) first ↔ schema.Holds (sources resolve last) last := by
  apply forall_congr'; intro equation
  apply forall_congr'; intro member
  have target := same equation.target (List.mem_flatMap.mpr ⟨equation,member,List.mem_cons_self ..⟩)
  have rhs := value_same resolve equation.mode equation.expression
    (fun name present => same name (List.mem_flatMap.mpr ⟨equation,member,List.mem_cons_of_mem _ present⟩))
  unfold Equation.Holds
  rw [target,rhs]

mutual
  theorem actual_reads (resolve : Mode → Nat → Nat) (expression : Expr) :
      reads resolve .actual expression = (GeneralNominalCenteredHeadMatExtension.names expression).map (resolve .actual) := by
    cases expression with
    | «variable» => rfl
    | primitive _ arguments | nominal _ arguments =>
        exact actual_readMany resolve arguments
    | record _ payload tail | join payload tail =>
        simp only [reads,GeneralNominalCenteredHeadMatExtension.names,List.map_append,
          actual_reads resolve payload,actual_reads resolve tail]
    | variant _ payload =>
        exact actual_reads resolve payload
  theorem actual_readMany (resolve : Mode → Nat → Nat) (expressions : List Expr) :
      readMany resolve .actual expressions = (GeneralNominalCenteredHeadMatExtension.namesMany expressions).map (resolve .actual) := by
    cases expressions with
    | nil => rfl
    | cons head rest => simp only [readMany,GeneralNominalCenteredHeadMatExtension.namesMany,
        List.map_append,actual_reads resolve head,actual_readMany resolve rest]
end
end Yulang.GeneralDictionaryDefaultModeSupport213
