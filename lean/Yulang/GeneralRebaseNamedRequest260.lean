import Yulang.GeneralRebaseRequestBodyKeys260
namespace Yulang.GeneralRebaseNamedRequest260
open GeneralRebaseStep258
open GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance

/-- Stable under reorderings of the current alias-class request list. The
finite-candidate membership argument is not supplied by this encoding. -/
def code (output : GeneralSourceState.Output) : Nat :=
 GeneralNominalIdentities.pair output.name output.target

theorem code_injective {first last : GeneralSourceState.Output} (same : code first = code last) : first = last := by
 have fields : (first.name,first.target) = (last.name,last.target) := GeneralNominalIdentities.pair_injective same
 cases first with
 | mk name target =>
   cases last with
   | mk name' target' =>
     have names := congrArg Prod.fst fields
     have targets := congrArg Prod.snd fields
     cases names
     cases targets
     rfl

def compile (plan : Plan roles) (owner kind : Nat) (output : GeneralSourceState.Output) :=
 GeneralRebaseRequestBodyKeys260.compile plan owner kind (code output) output

theorem outputs_separate (owner kind : Nat) (first last : GeneralSourceState.Output) (different : first ≠ last)
 (firstSchema lastSchema : GeneralNominalCenteredHeadMatSchemas.Schema) (fact : Fact) :
 ¬ (fact ∈ GeneralRebaseOwnedOutputKeys260.keys (GeneralRebaseRequestBodyKeys260.space owner kind (code first)) firstSchema ∧
 fact ∈ GeneralRebaseOwnedOutputKeys260.keys (GeneralRebaseRequestBodyKeys260.space owner kind (code last)) lastSchema) := by
 apply GeneralRebaseRequestBodyKeys260.requests_separate
 intro same
 exact different (code_injective same)

theorem lookup_unique (plan : Plan roles) (output : GeneralSourceState.Output) (first last : Body)
 (one : lookup roles plan.packet.declaration output.name = some first)
 (two : lookup roles plan.packet.declaration output.name = some last) : first = last :=
 Option.some.inj (one.symm.trans two)

theorem equation_meaning (plan : Plan roles) (owner kind : Nat) (output : GeneralSourceState.Output)
 (body : Body) (assignment : GeneralNominalCommonBridge.Assignment) :
 (∀ fact ∈ GeneralRebaseOwnedOutputKeys260.keys (GeneralRebaseRequestBodyKeys260.space owner kind (code output))
   (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body),
 GeneralRebaseOwnedOutputKeys260.Holds (GeneralRebaseRequestBodyKeys260.space owner kind (code output))
   (GeneralNominalCenteredHeadMatEffects.bodySchema plan output.target body)
   (GeneralNominalVersionedEffects231.bodyVariables plan assignment body) assignment fact) ↔
 GeneralNominalVersionedEffects231.BodyHolds plan output.target assignment body :=
 GeneralRebaseRequestBodyKeys260.equation_meaning ..

theorem probe_repaired :
 compile GeneralDictionaryDefaultGap206Source.plan 37 2 ⟨0,0⟩ ≠
 compile GeneralDictionaryDefaultGap206Source.plan 37 2 ⟨0,1⟩ := by
 intro same
 have lists := Except.ok.inj same
 have heads := (List.cons.inj lists).1
 have spaces := Fact.installed.inj heads
 have requests := (GeneralRebaseRequestBodyKeys260.space_identity spaces).2.2
 have outputs := code_injective requests
 have targets := congrArg GeneralSourceState.Output.target outputs
 cases targets
end Yulang.GeneralRebaseNamedRequest260
