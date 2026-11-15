import Yulang.GeneralDictionaryDefaultModeSupport212

/-! Shared materialization targets need compatible right sides, not distinct
source identities. This construction keeps all repeated equations. -/
namespace Yulang.GeneralDictionaryDefaultSharedTargets212
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCenteredHeadMatExtension (sources extend)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDictionaryDefaultModeSupport212 (Independent value_same)
open CommonNominalFullCarrier
variable {schema : Schema} {before : Assignment}

 def Compatible (resolve : GeneralNominalMaterialization.Mode → Nat → Nat)
     (model : Assignment) (equations : List Equation) : Prop :=
  ∀ first ∈ equations, ∀ last ∈ equations, first.target = last.target →
    Equivalent (value (sources resolve model) first.mode first.expression)
      (value (sources resolve model) last.mode last.expression)

 theorem chosen {equations : List Equation} {equation : Equation} (member : equation ∈ equations) :
     ∃ selected, equations.find? (fun other : Equation => other.target == equation.target) = some selected ∧
       selected ∈ equations ∧ selected.target = equation.target := by
  cases found : equations.find? (fun other : Equation => other.target == equation.target) with
  | none => exact False.elim ((List.find?_eq_none.mp found) equation member (by simp))
  | some selected => exact ⟨selected,rfl,List.mem_of_find?_eq_some found,(by simpa using List.find?_some found)⟩

 theorem extend_holds (independent : Independent resolve schema.equations)
     (compatible : Compatible resolve before schema.equations) :
     schema.Holds (sources resolve (extend resolve before schema.equations))
       (extend resolve before schema.equations) := by
  intro equation member
  obtain ⟨selected,found,present,target⟩ := chosen member
  have rhs := value_same resolve equation.mode equation.expression
    (first := extend resolve before schema.equations) (last := before)
    (fun name used => GeneralNominalCenteredHeadMatExtension.extend_outside (independent equation member name used))
  unfold Equation.Holds
  rw [rhs]
  simp only [extend,found]
  exact compatible selected present equation member target

 theorem journal_extension (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
     (valid : GeneralNominalCenteredHeadMatStepJournal.Models state before)
     (independent : Independent resolve schema.equations)
     (compatible : Compatible resolve before schema.equations)
     (fresh : ∀ equation ∈ schema.equations,
       equation.target ∉ GeneralDictionaryDefaultJournalFrame212.journalSources state) :
     ∃ after, GeneralNominalCenteredHeadMatStepJournal.Models state after ∧
       schema.Holds (sources resolve after) after ∧
       Agree (GeneralDictionaryDefaultJournalFrame212.journalSources state) before after := by
  have same : Agree (GeneralDictionaryDefaultJournalFrame212.journalSources state) before
      (extend resolve before schema.equations) := by
    intro name member
    symm
    apply GeneralNominalCenteredHeadMatExtension.extend_outside
    rintro present
    obtain ⟨equation,within,rfl⟩ := List.mem_map.mp present
    exact fresh equation within member
  exact ⟨extend resolve before schema.equations,
    (GeneralDictionaryDefaultJournalFrame212.models_iff state same).mp valid,
    extend_holds independent compatible,same⟩

end Yulang.GeneralDictionaryDefaultSharedTargets212
