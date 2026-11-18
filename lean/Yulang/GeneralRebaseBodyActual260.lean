import Yulang.GeneralReflexiveDefaultRegression260
namespace Yulang.GeneralRebaseBodyActual260
open GeneralRebaseStep258

/-- The explicit fixture composes its actual capture report with the actual
requested class body. Duplicate installed markers are normalized away. -/
def explicitProposal : Option Proposal := do
 let captures ← GeneralRebaseFiniteReport259.compile 0 GeneralOutputRebaseSource260.atom
   (GeneralNominalPacketSupport.report GeneralDictionaryOutputDepth252.packet)
 match GeneralRebaseBodyDecoder260.compile GeneralDictionaryOutputDepth252.plan 0 ⟨0,3⟩ with
 | .error _ => none
 | .ok body => some ((captures ++ body).eraseDups)

theorem explicit_exact : explicitProposal = some GeneralOutputRebaseSource260.facts := by
 unfold explicitProposal
 rw [GeneralOutputRebaseSource260.capture_exact]
 rfl

theorem distinct_default_target :
 GeneralRebaseBodyDecoder260.compile GeneralDictionaryDefaultGap206Source.plan 37 ⟨0,0⟩ =
 .ok GeneralDefaultRebaseSource260.facts := rfl

theorem reflexive_default_target :
 GeneralRebaseBodyDecoder260.compile GeneralDictionaryAllocDefaultSource202.plan 37 ⟨0,1⟩ =
 .ok GeneralReflexiveDefaultSource260.facts := rfl

/-- Identical finite addresses in different source layouts do not identify
what their equations mean; the request target is part of the fixed layout. -/
theorem target_not_interchangeable :
 GeneralNominalCenteredHeadMatEffects.bodySchema GeneralDictionaryDefaultGap206Source.plan 0 GeneralDefaultRebaseBody260.body ≠
 GeneralNominalCenteredHeadMatEffects.bodySchema GeneralDictionaryAllocDefaultSource202.plan 1 GeneralReflexiveDefaultSource260.body := by
 intro equal
 have equations := congrArg GeneralNominalCenteredHeadMatSchemas.Schema.equations equal
 change ([⟨0,.actual,.variable 0⟩] : List GeneralNominalCenteredHeadMatSchemas.Equation) = [⟨1,.actual,.variable 0⟩] at equations
 have same := List.cons.inj equations
 have targets := congrArg GeneralNominalCenteredHeadMatSchemas.Equation.target same.1
 cases targets
end Yulang.GeneralRebaseBodyActual260
