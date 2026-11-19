import Yulang.GeneralRebaseMergeScan267
import Yulang.GeneralRebaseInstallCoverage267

namespace Yulang.GeneralRebaseStrictSourceCases267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalSaturationState (Generated Alias)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedInstallStep232 (Committed)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedAdministrative232 (merge)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded)
open GeneralRebaseLiveProjection264 (project)
open GeneralSourceState (Output)

def InstallCase (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
 ∃ effect : Effect roles,
 Generated before.core.erased.current root effect.plan.packet.site.occurrence ∧
 Installable (Encoded registry) before effect ∧ ¬ Committed before effect.plan ∧
 after = install before effect

def MergeCase (root : Occurrence roles) (before after : State roles) : Prop :=
 ∃ first last : Site roles,
 first ∈ before.core.sites ∧ last ∈ before.core.sites ∧
 Generated before.core.erased.current root first.occurrence ∧
 SameInputs (Models before) first last ∧
 ¬ Alias before.core.erased.current first.occurrence.identity last.occurrence.identity ∧
 after = merge before first last

theorem operational (registry : Registry) (root : Occurrence roles) (before after : State roles)
 (cases : InstallCase registry root before after ∨ MergeCase root before after) :
 (Boundary roles).Step registry root before after := by
 rcases cases with ⟨effect,generated,enabled,novel,rfl⟩ | ⟨a,b,one,two,generated,same,openPair,rfl⟩
 · exact ⟨_,generated,.install effect enabled novel⟩
 · exact ⟨_,generated,.merge a b one two same openPair⟩

/-- All strict projected source steps on actual reachable states are either
installs or merges. This is not a dichotomy for all concrete source steps. -/
theorem strict_inversion (registry : Registry) (root : Occurrence roles) (before after : State roles)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root before)
 (step : (Boundary roles).Step registry root before after)
 (owners : List Nat) (pool : List Output) (changed : project owners pool after ≠ project owners pool before) :
 InstallCase registry root before after ∨ MergeCase root before after := by
 obtain ⟨focus,generated,atFocus⟩ := step
 cases atFocus with
 | administrative action =>
   cases action with
   | enqueue linked absent =>
     obtain ⟨site,listed,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
       (GeneralNominalVersionedMixedTrace235.reachable reachable).1 generated
     exact False.elim (absent site listed same)
   | refresh context _ _ _ _ _ =>
     exact False.elim (changed (GeneralRebaseSourceProjection264.refresh_stutters owners pool before context).symm)
   | reobserve revision _ _ =>
     exact False.elim (changed (GeneralRebaseSourceProjection264.reobserve_stutters owners pool before revision).symm)
   | equate a b _ _ _ _ =>
     exact False.elim (changed (GeneralRebaseSourceProjection264.equate_stutters owners pool before a b).symm)
 | refresh focus context _ _ _ _ _ =>
   exact False.elim (changed (GeneralRebaseSourceProjection264.refresh_stutters owners pool before context).symm)
 | install effect enabled novel => exact Or.inl ⟨effect,generated,enabled,novel,rfl⟩
 | merge first last a b same openPair => exact Or.inr ⟨first,last,a,b,generated,same,openPair,rfl⟩

end Yulang.GeneralRebaseStrictSourceCases267
