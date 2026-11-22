import Yulang.GeneralDeclarativeTaggedFixtureSelection340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeTaggedFixtureModel340
open GeneralDeclarativeTaggedFixture340
open GeneralDeclarativeTaggedFixtureSelection340 (classification)
open GeneralDeclarativeHiddenDecl324 (interpretation)
open GeneralDeclarativeTaggedSelected340 (local_sound)
open GeneralDeclarativeTaggedDictionary340 (dictionary_sound)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeGrowth327 (facts restrict)
open GeneralDeclarativeTaggedPatch340 (patch)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
open GeneralNominalCommonBridge (Assignment variant_merge)
open CommonNominalFullCarrier (Ty Equivalent variant subtype_refl common_variant_iff)

abbrev int : Ty := .base .int
abbrev boolean : Ty := .base .bool
abbrev actualRoot : Ty := .union (variant 7 int) (variant 7 boolean)
abbrev entire : Ty := .union int boolean
def startModel : Assignment := fun n =>
  (if n < 3 then actualRoot else if n = 6 then entire else int,Common.rowEmpty)

theorem initial_fits : Models initial startModel := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro r used
    rcases List.mem_cons.mp used with rfl|other
    · exact subtype_refl _
    · cases List.mem_singleton.mp other
      exact subtype_refl _
  · intro e used
    rcases List.mem_cons.mp used with rfl|other
    · exact eqv_refl _
    · cases List.mem_singleton.mp other
      exact eqv_refl _

theorem both_shares (m : Assignment) : GeneralDeclarativeStableCanonical329.EqualUses m spans := by
  intro key first last f l
  obtain ⟨_,_,same⟩ := List.mem_map.mp f
  obtain ⟨_,_,other⟩ := List.mem_map.mp l
  have e : selectedCap = first := congrArg Prod.snd same
  have g : selectedCap = last := congrArg Prod.snd other
  rw [← e,← g]
  exact eqv_refl _

theorem complete_models : ∃ m, ModelsExact endState [] m ∧
    Equivalent (m selectedCap.center).1 entire ∧ (m 6).1 = entire := by
  obtain ⟨first,firstFit,kept⟩ := keep_old_model.lifts startModel initial_fits
  have ranges := (GeneralDeclarativeTaggedInputs340.complete inputs
    (GeneralDeclarativeClauseBatch327.reflexive _)).2.1
  have assembly := GeneralDeclarativeStableAssemble329.assemble keep spans fallback ranges
  obtain ⟨m,mergedFit,agrees⟩ :=
    (GeneralDeclarativeStableAssemble329.witness_projection assembly first).mp ⟨firstFit,both_shares first⟩
  have fits := restrict (GeneralDeclarativeGrowth327.trans (facts _ _) assembly.preserve.grows) m mergedFit
  have origin : (m 1).1 = actualRoot := by
    have x : m 1 = first 1 := agrees _ (by decide +kernel)
    have y : first 1 = startModel 1 := kept _ (by decide +kernel)
    rw [x,y]
    rfl
  have outputFixed : (m 6).1 = entire := by
    rw [agrees 6 (List.mem_append_right _ List.mem_cons_self),
      kept 6 (List.mem_append_right _ List.mem_cons_self)]
    rfl
  have early := restrict (facts _ _) m fits
  have tag : Equivalent (m 1).1 (variant 7 (m selectedCap.center).1) :=
    semantic (patch read keep).2.2 m early
  rw [origin] at tag
  have payloadEquiv := eqv_trans (eqv_symm tag) (variant_merge 7 int boolean)
  have exactPayload : Equivalent (m selectedCap.center).1 entire :=
    ⟨(common_variant_iff ..).mp payloadEquiv.1,(common_variant_iff ..).mp payloadEquiv.2⟩
  have finalFits : Models endState m := by
    unfold endState
    refine (model_append m).mpr ⟨mergedFit,?_⟩
    intro row here
    cases List.mem_singleton.mp here
    change Equivalent (m 6).1 (m selectedCap.center).1
    rw [outputFixed]
    exact eqv_symm exactPayload
  exact ⟨m,⟨finalFits,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩,
    exactPayload,outputFixed⟩

/-- Complete concrete pure-join selection; fixed target 6 describes
the whole payload, not one selected branch. -/
theorem actual_dictionary : ∃ m, ModelsExact endState [] m ∧ Evidence registry interpretation m d (.node 97 []) ∧
    Equivalent (m selectedCap.center).1 entire ∧ (m 6).1 = entire := by
  obtain ⟨m,fits,same,fixed⟩ := complete_models
  exact ⟨m,fits,dictionary_sound checked covered wanted classification fits,same,fixed⟩

end Yulang.GeneralDeclarativeTaggedFixtureModel340
