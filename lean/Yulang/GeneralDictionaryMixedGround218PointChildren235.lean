import Yulang.GeneralDictionaryMixedGround218PointUniform235
import Yulang.GeneralNominalVersionedMixedQuietInstall235
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedGround218PointChildren235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (clause)
open GeneralDictionaryGroundCopy218Reinstall (newChild)
open GeneralDictionaryGroundCopy218SaturatedParent (planFor packetFor)
open GeneralDictionaryMixedGround218PointUniform235 (capture)
variable (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
  (ordinary : List (PresenceNormalForm.Atom Nat))

theorem child_arguments (valid : clause.Signature roles) (i) :
    (GeneralNominalVersionedFrame231.childSite (planFor allocated reserved ordinary) clause valid).occurrence.demand.arguments i =
      newChild.occurrence.demand.arguments i := by
  change Fin 2 at i
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl | rfl
  · change (GeneralNominalVersionedFrame231.capture (packetFor allocated reserved ordinary)).inputs 0 = _
    rw [capture 0 (Or.inl rfl),GeneralDictionaryGroundCopy218Reinstall.child_arguments]
    rfl
  · change (GeneralNominalVersionedFrame231.capture (packetFor allocated reserved ordinary)).inputs 1 = _
    rw [capture 1 (Or.inr rfl),GeneralDictionaryGroundCopy218Reinstall.child_arguments]
    rfl

theorem children_eq : GeneralNominalVersionedFrame231.children (packetFor allocated reserved ordinary) =
    [newChild.occurrence] := by
  unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralDictionaryGroundCopy218Install.canonical_declaration]
  change [GeneralNominalVersionedFrame231.clauseChild (packetFor allocated reserved ordinary) clause _] = [newChild.occurrence]
  apply congrArg List.singleton
  apply congrArg (fun arguments : Fin 2 → GeneralSourceState.Interval =>
    (⟨GeneralNominalCenters.fresh 7 0 0 6 0 0,⟨1,arguments,[],by intro _ h; cases h⟩⟩ : GeneralSourceDictionaries.Occurrence roles))
  funext i
  exact child_arguments allocated reserved ordinary (GeneralDictionaryGroundCopy218Install.declaration_checked.signature.2.2.2 _ (List.mem_singleton_self _)) i

theorem quiet : GeneralNominalVersionedMixedQuietInstall235.Quiet (planFor allocated reserved ordinary) := by
  intro child member
  rw [children_eq] at member
  cases List.mem_singleton.mp member
  rfl
end Yulang.GeneralDictionaryMixedGround218PointChildren235
