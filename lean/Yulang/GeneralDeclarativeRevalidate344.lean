import Yulang.GeneralDeclarativeTwoViews344
import Yulang.GeneralDeclarativeStampedReplay344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRevalidate344
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralWhereVersionInstall317 (Journal InstallStep install Models emitted)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralDeclarativeCommitPackage344 (Witness)
open GeneralDeclarativeReplayOrder344 (SameBirth logicalChildren)
open GeneralDeclarativeEffectiveReplay344 (appendModes)
open GeneralDeclarativeModeBridge343 (recovered rows)
open GeneralDeclarativeEntailment320 (Holds model_append)
open GeneralStoppedOrdinarySite335 (demand)
open GeneralDeclarativeHead320 (Equation State)
open GeneralDeclarativeClauseBatch327 (Port)
open GeneralDeclarativeDemand320 (Demand)
open CommonRoleOutermostResolver (All₂)

private theorem length_eq {p : α → β → Prop} {a : List α} {b : List β} (h : All₂ p a b) :
    a.length = b.length := by
  induction h with
  | nil => rfl
  | cons _ _ tail => exact congrArg Nat.succ tail

/-- Each of the old positional aliases is an actual row of the
constructed view. On revaluation they give all birth argument
meanings again; no model-only reclassification or new origin. -/
theorem birth {ss : List (Site rs)} {ds : List Demand} {m n : Assignment}
    (old : All₂ (SameBirth m) ss ds)
    (valid : ∀ row ∈ appendModes ss ds, Holds n row) :
    All₂ (SameBirth n) ss ds := by
  induction old with
  | nil => exact .nil
  | @cons s d ss ds head _ rest =>
    have here := recovered (demand s).arguments d.arguments (length_eq head.arguments)
      (fun row found => valid row (List.mem_append_left _ found))
    exact .cons ⟨head.role,here,head.targets⟩
      (rest (fun row h => valid row (List.mem_append_right _ h)))

theorem replay {j : Journal rs} {p : Plan rs} {m x n : Assignment}
    {keep : List Nat} {before s : State} {ports : List Port} {whereRows rootRows : List Equation}
    (old : Witness j p m x keep before s ports whereRows rootRows)
    (fit : Models j n) (ordinary : GeneralDeclarativeHead320.Models s n)
    (preserved : ∀ k ∈ journalSources j, n k = m k)
    (protectedNames : ∀ k ∈ keep, n k = m k) :
    Witness j p m n keep before s ports whereRows rootRows := by
  have modeling := ordinary
  rw [old.shape] at modeling
  have names := ((model_append n).mp modeling).2
  exact ⟨fit,preserved,protectedNames,old.inputBatch,old.whereBatch,old.rootBatch,
    old.literalRootTargets,ordinary,old.shape,birth old.birth names,old.effective⟩

/-- Stronger simultaneous replay. Both full receipt witnesses, not
only modeled views, hold in the one final journal-preserving
assignment. Their two physical occurrences are not merged. -/
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
      Witness a p₁ m final (journalSources b ++ protect) prepA viewA portsA whereA rootA ∧
      Witness b p₂ mid final ((journalSources a ++ GeneralDeclarativeFootprint321.stateNames viewA) ++ protect)
        prepB viewB portsB whereB rootB ∧
      (∀ k ∈ protect, final k = m k) := by
  let a := install before₁ ctx₁ p₁
  let b := install before₂ ctx₂ p₂
  obtain ⟨prepA,viewA,portsA,whereA,rootA,mid,prepB,viewB,portsB,whereB,rootB,final,
    wA,wB,rawA,rawB,typedA,typedB,protectedNames⟩ :=
    GeneralDeclarativeTwoViews344.together r before₁ before₂ ctx₁ ctx₂ p₁ p₂
      step₁ step₂ m first second ready₁ ready₂ protect
  have keepA : ∀ k ∈ journalSources a, final k = m k := fun k h =>
    (wB.kept k (List.mem_append_left _ (List.mem_append_left _ h))).trans (wA.preserved k h)
  have keepB : ∀ k ∈ journalSources b, final k = m k := fun k h =>
    (wB.preserved k h).trans (wA.kept k (List.mem_append_left _ h))
  have rewA : Witness a p₁ m final (journalSources b ++ protect) prepA viewA portsA whereA rootA :=
    replay wA rawA typedA keepA (fun k h => (List.mem_append.mp h).elim (keepB k) (protectedNames k))
  -- Only the first journal's source names and the external protect list
  -- are fixed relative to the original initial model in the second view.
  -- The first ordinary view contains fresh names, so keep it relative to mid.
  exact ⟨prepA,viewA,portsA,whereA,rootA,mid,prepB,viewB,portsB,whereB,rootB,final,
    rewA,wB,protectedNames⟩

end Yulang.GeneralDeclarativeRevalidate344
