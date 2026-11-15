import Yulang.GeneralDictionaryDefaultExpression209
import Yulang.GeneralDictionaryDefaultSharedTargets212
import Yulang.GeneralDictionaryDefaultJournalSupport213
import Yulang.GeneralNominalFramedExtension181

/-! Finite total equations with retained targets. Existing semantic values may
be reused; targets need neither be fresh nor distinct. This is an extension
construction, not a derivation of compatibility from selected nodes. -/
namespace Yulang.GeneralDictionaryDefaultOverlap214
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCenteredHeadMatExtension (sources extend)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDictionaryDefaultModeSupport212 (reads value_same)
open GeneralDictionaryDefaultSharedTargets212 (Compatible chosen)
open CommonNominalFullCarrier
variable {schema : Schema} {before : Assignment}

noncomputable def extendKeeping (keep : List Nat) (resolve : GeneralNominalMaterialization.Mode → Nat → Nat)
    (before : Assignment) (equations : List Equation) : Assignment :=
  GeneralDictionaryDefaultModelGlue212.splice keep before (extend resolve before equations)

theorem kept (member : name ∈ keep) :
    extendKeeping keep resolve before equations name = before name := by
  simp [extendKeeping,GeneralDictionaryDefaultModelGlue212.splice,member]

theorem outside (absent : name ∉ equations.map Equation.target) :
    extendKeeping keep resolve before equations name = before name := by
  classical
  by_cases member : name ∈ keep
  · exact kept member
  · simp only [extendKeeping,GeneralDictionaryDefaultModelGlue212.splice,member,ite_false]
    exact GeneralNominalCenteredHeadMatExtension.extend_outside absent

/-- Only writes outside the retained support must be absent from RHS reads. -/
def ReadsRetained (keep : List Nat) (resolve : GeneralNominalMaterialization.Mode → Nat → Nat)
    (equations : List Equation) : Prop :=
  ∀ equation ∈ equations, ∀ name ∈ reads resolve equation.mode equation.expression,
    name ∈ keep ∨ name ∉ equations.map Equation.target

def Overlap (keep : List Nat) (resolve : GeneralNominalMaterialization.Mode → Nat → Nat)
    (before : Assignment) (equations : List Equation) : Prop :=
  ∀ equation ∈ equations, equation.target ∈ keep →
    Equivalent (before equation.target).1
      (value (sources resolve before) equation.mode equation.expression)

theorem rhs_same (retained : ReadsRetained keep resolve schema.equations)
    (member : equation ∈ schema.equations) :
    value (sources resolve (extendKeeping keep resolve before schema.equations)) equation.mode equation.expression =
      value (sources resolve before) equation.mode equation.expression := by
  apply value_same
  intro name used
  rcases retained equation member name used with inside | absent
  · exact kept inside
  · exact outside absent

theorem holds (retained : ReadsRetained keep resolve schema.equations)
    (compatible : Compatible resolve before schema.equations)
    (overlap : Overlap keep resolve before schema.equations) :
    schema.Holds (sources resolve (extendKeeping keep resolve before schema.equations))
      (extendKeeping keep resolve before schema.equations) := by
  classical
  intro equation member
  unfold Equation.Holds
  rw [rhs_same retained member]
  by_cases inside : equation.target ∈ keep
  · rw [kept inside]
    exact overlap equation member inside
  · obtain ⟨selected,found,present,target⟩ := chosen member
    simp only [extendKeeping,GeneralDictionaryDefaultModelGlue212.splice,inside,ite_false,extend,found]
    exact compatible selected present equation member target

theorem journal_extension (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (valid : GeneralNominalCenteredHeadMatStepJournal.Models state before)
    (retained : ReadsRetained (GeneralDictionaryDefaultJournalSupport213.journalSources state) resolve schema.equations)
    (compatible : Compatible resolve before schema.equations)
    (overlap : Overlap (GeneralDictionaryDefaultJournalSupport213.journalSources state) resolve before schema.equations) :
    ∃ after, GeneralNominalCenteredHeadMatStepJournal.Models state after ∧
      schema.Holds (sources resolve after) after ∧
      Agree (GeneralDictionaryDefaultJournalSupport213.journalSources state) before after := by
  let after := extendKeeping (GeneralDictionaryDefaultJournalSupport213.journalSources state) resolve before schema.equations
  have same : Agree (GeneralDictionaryDefaultJournalSupport213.journalSources state) before after :=
    fun _ member => (kept member).symm
  exact ⟨after,(GeneralDictionaryDefaultJournalSupport213.models_iff state same).mp valid,
    holds retained compatible overlap,same⟩
end Yulang.GeneralDictionaryDefaultOverlap214

namespace Yulang.GeneralDictionaryDefaultOverlap214
open GeneralNominalCenteredHeadMatExpressions GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCenteredHeadMatExtension (sources)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDictionaryDefaultSharedTargets212 (Compatible)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier
variable {schema : Schema} {before after : Assignment}

/-- Any solution whose RHS values are retained forces both compatibility and
agreement at retained targets. This detects contradictory duplicate equations. -/
theorem necessary
    (solution : schema.Holds (sources resolve after) after)
    (keeps : Agree keep before after)
    (rhs : ∀ equation ∈ schema.equations,
      value (sources resolve after) equation.mode equation.expression =
      value (sources resolve before) equation.mode equation.expression) :
    Compatible resolve before schema.equations ∧ Overlap keep resolve before schema.equations := by
  have held equation (member : equation ∈ schema.equations) :
      Equivalent (after equation.target).1
        (value (sources resolve before) equation.mode equation.expression) := by
    have good := solution equation member
    unfold Equation.Holds at good
    rwa [rhs equation member] at good
  constructor
  · intro first one last two same
    have a := held first one
    have b := held last two
    rw [same] at a
    exact equivalent_trans ⟨a.2,a.1⟩ b
  · intro equation member inside
    rw [keeps _ inside]
    exact held equation member

/-- Exact criterion for RHS-preserving equation extension, without fresh or
unique targets. This does not assert the criterion for arbitrary selected nodes. -/
theorem solution_iff (retained : ReadsRetained keep resolve schema.equations) :
    (∃ after, Agree keep before after ∧ schema.Holds (sources resolve after) after ∧
      ∀ equation ∈ schema.equations,
        value (sources resolve after) equation.mode equation.expression =
          value (sources resolve before) equation.mode equation.expression) ↔
    Compatible resolve before schema.equations ∧ Overlap keep resolve before schema.equations := by
  constructor
  · rintro ⟨after,same,solution,rhs⟩
    exact necessary solution same rhs
  · rintro ⟨compatible,overlap⟩
    exact ⟨extendKeeping keep resolve before schema.equations,
      fun _ member => (kept member).symm,holds retained compatible overlap,fun _ member => rhs_same retained member⟩
end Yulang.GeneralDictionaryDefaultOverlap214
