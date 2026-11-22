import Yulang.GeneralDeclarativePackageBoundary344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTwoViews344
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralWhereVersionInstall317 (Journal InstallStep install Models)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralDeclarativeCommitPackage344 (Witness)
open GeneralDeclarativePackageBoundary344 (actual)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeClauseBatch327 (Port)

/-- Compose the ordinary replays of two real commits without
identifying their captures, sites, or output lists. Both compiled
views and both raw journals then share one final assignment. -/
theorem together (r : Registry) (before₁ before₂ : Journal rs)
    (ctx₁ ctx₂ : GeneralNominalCandidates.Context) (p₁ p₂ : Plan rs)
    (step₁ : InstallStep r before₁ (install before₁ ctx₁ p₁))
    (step₂ : InstallStep r before₂ (install before₂ ctx₂ p₂))
    (m : Assignment) (first : Models (install before₁ ctx₁ p₁) m)
    (second : Models (install before₂ ctx₂ p₂) m)
    (ready₁ : Ready (install before₁ ctx₁ p₁).mixed.core p₁.packet.site.occurrence p₁)
    (ready₂ : Ready (install before₂ ctx₂ p₂).mixed.core p₂.packet.site.occurrence p₂)
    (protect : List Nat) :
    let a := install before₁ ctx₁ p₁
    let b := install before₂ ctx₂ p₂
    ∃ prepA viewA portsA whereA rootA mid prepB viewB portsB whereB rootB final,
      Witness a p₁ m mid (journalSources b ++ protect) prepA viewA portsA whereA rootA ∧
      Witness b p₂ mid final ((journalSources a ++ stateNames viewA) ++ protect) prepB viewB portsB whereB rootB ∧
      Models a final ∧ Models b final ∧
      GeneralDeclarativeHead320.Models viewA final ∧ GeneralDeclarativeHead320.Models viewB final ∧
      (∀ k ∈ protect, final k = m k) := by
  let a := install before₁ ctx₁ p₁
  let b := install before₂ ctx₂ p₂
  obtain ⟨prepA,viewA,portsA,whereA,rootA,mid,wA⟩ :=
    actual step₁ m first (journalSources b ++ protect) ready₁
  have staysB : Models b mid := by
    apply (journal_models b (fun k h => (wA.kept k (List.mem_append_left _ h)).symm)).mp
    exact second
  obtain ⟨prepB,viewB,portsB,whereB,rootB,final,wB⟩ :=
    actual step₂ mid staysB ((journalSources a ++ stateNames viewA) ++ protect) ready₂
  refine ⟨prepA,viewA,portsA,whereA,rootA,mid,prepB,viewB,portsB,whereB,rootB,final,
    wA,wB,?_,wB.raw,?_,wB.ordinary,?_⟩
  · exact (journal_models a (fun k h =>
      (wB.kept k (List.mem_append_left _ (List.mem_append_left _ h))).symm)).mp wA.raw
  · exact (preserves_models viewA (fun k h =>
      (wB.kept k (List.mem_append_left _ (List.mem_append_right _ h))).symm)).mp wA.ordinary
  · intro k h
    exact (wB.kept k (List.mem_append_right _ h)).trans (wA.kept k (List.mem_append_right _ h))

end Yulang.GeneralDeclarativeTwoViews344
