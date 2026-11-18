import Yulang.GeneralRebaseNamedRequest260
namespace Yulang.GeneralRebaseBodyTable261
open GeneralRebaseStep258
open GeneralNominalCenters
open GeneralSourceState (Output)
open GeneralDictionaryAssociatedProvenance
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatSchemas (Schema)

/-- Missing bodies remain marked unknown. Their empty equation list alone is
not a readiness or language-acceptance certificate. -/
def schema (plan : Plan roles) (output : Output) : Schema :=
 match lookup roles plan.packet.declaration output.name with
 | none => ⟨[],true⟩
 | some body => GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body

def variables (plan : Plan roles) (output : Output) (assignment : Assignment) :=
 match lookup roles plan.packet.declaration output.name with
 | none => fun (_ : GeneralNominalMaterialization.Mode) (_ : Nat) => (.bottom : CommonNominalFullCarrier.Ty)
 | some body => GeneralNominalVersionedEffects231.bodyVariables plan assignment body

def address (owner : Nat) (output : Output) := GeneralRebaseRequestBodyKeys260.space owner 1 (GeneralRebaseNamedRequest260.code output)
def keys (plan : Plan roles) (owner : Nat) (output : Output) := GeneralRebaseOwnedOutputKeys260.keys (address owner output) (schema plan output)
def facts (plan : Plan roles) (owner : Nat) (outputs : List Output) : List Fact := outputs.flatMap (keys plan owner)

def localHolds (plan : Plan roles) (owner : Nat) (output : Output) (assignment : Assignment) :=
 GeneralRebaseOwnedOutputKeys260.Holds (address owner output) (schema plan output) (variables plan output assignment) assignment

/-- A fact means every obligation assigned that address by this fixed table.
Address injectivity below ensures distinct named requests do not collide. -/
def Holds (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) (fact : Fact) : Prop :=
 ∀ output ∈ outputs, fact ∈ keys plan owner output → localHolds plan owner output assignment fact

theorem schema_meaning (plan : Plan roles) (output : Output) (assignment : Assignment) :
 (schema plan output).Holds (variables plan output assignment) assignment ↔
 ∀ body, lookup roles plan.packet.declaration output.name = some body →
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body := by
 cases found : lookup roles plan.packet.declaration output.name with
 | none => simp [schema,variables,found,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
 | some body => simp [schema,variables,found,GeneralNominalVersionedEffects231.BodyHolds]

theorem translated (plan : Plan roles) (output : Output) :
 (schema plan output).unknown = false ↔
 ∃ body, lookup roles plan.packet.declaration output.name = some body ∧
 (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body).unknown = false := by
 cases found : lookup roles plan.packet.declaration output.name with
 | none => simp [schema,found]
 | some body => simp [schema,found]

theorem member (plan : Plan roles) (owner : Nat) (outputs : List Output) (fact : Fact) :
 fact ∈ facts plan owner outputs ↔ ∃ output ∈ outputs, fact ∈ keys plan owner output := by
 simp only [facts,List.mem_flatMap]

theorem local_exact (plan : Plan roles) (owner : Nat) (output : Output) (assignment : Assignment) :
 (∀ fact ∈ keys plan owner output, localHolds plan owner output assignment fact) ↔
 ∀ body, lookup roles plan.packet.declaration output.name = some body →
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body :=
 (GeneralRebaseOwnedOutputKeys260.all_exact ..).trans (schema_meaning ..)

theorem all_exact (plan : Plan roles) (owner : Nat) (outputs : List Output) (assignment : Assignment) :
 (∀ fact ∈ facts plan owner outputs, Holds plan owner outputs assignment fact) ↔
 ∀ output ∈ outputs, ∀ body, lookup roles plan.packet.declaration output.name = some body →
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body := by
 constructor
 · intro valid output included
   apply (local_exact plan owner output assignment).mp
   intro fact within
   exact valid fact ((member ..).mpr ⟨output,included,within⟩) output included within
 · intro valid fact _ output included within
   exact (local_exact plan owner output assignment).mpr (valid output included) fact within

theorem different_requests (plan : Plan roles) (owner : Nat) (first last : Output)
 (different : first ≠ last) (fact : Fact) :
 ¬ (fact ∈ keys plan owner first ∧ fact ∈ keys plan owner last) :=
 GeneralRebaseNamedRequest260.outputs_separate owner 1 first last different _ _ fact

theorem reordered (plan : Plan roles) (owner : Nat) (first last : List Output)
 (same : ∀ output, output ∈ first ↔ output ∈ last) (assignment : Assignment) :
 (∀ fact ∈ facts plan owner first, Holds plan owner first assignment fact) ↔
 (∀ fact ∈ facts plan owner last, Holds plan owner last assignment fact) := by
 rw [all_exact,all_exact]
 constructor
 · intro valid output inside; exact valid output ((same output).mpr inside)
 · intro valid output inside; exact valid output ((same output).mp inside)
end Yulang.GeneralRebaseBodyTable261
