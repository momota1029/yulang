import Yulang.GeneralWhereVersionSemantics317
import Yulang.GeneralWhereVersionLeafSelect317
import Yulang.GeneralWhereVersionRefine317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 45000000
/-! An isolated successor installation. It appends genuine compiled sites
and edges, but does not append the impossible old-format root packet.
The corrected root plan is a separate journal entry with its own equations. -/
namespace Yulang.GeneralWhereVersionInstall317
open GeneralDeclarations GeneralNominalCenters GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCommonBridge (Assignment)
open GeneralWhereVersionCompiler317 (child children emissions)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionCommit317 (core framedState compiled_models)
open GeneralWhereVersionSnapshot317 (context)
open GeneralLiveCompoundLeafInstall316 (after reachable)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundPostRootHead316 (frame)
open GeneralLiveCompoundPostRootSelect316 (selected)
open GeneralLiveCompoundChildSite316 (signature)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry boundary_checked otherChild)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralWhereVersionCase317 (site)
open GeneralVersionedHistoryEvidence310 (Compiled)

def emitted (p : Plan rs) : List (Site rs) :=
  (GeneralCanonicalChildOrder.canonicalRequirements p.packet.declaration.requirements).attach.map fun clause =>
    child p clause.val (p.packet.checked.signature.2.2.2 clause.val
      ((GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property))

theorem ordered (p : Plan rs) : (emitted p).map Site.occurrence = children p := by
  unfold emitted children emissions GeneralCanonicalChildOrder.canonicalEmit GeneralDeclarationDemands.emitAll
  simp only [List.map_map]
  rfl

def installCore (before : GeneralNominalCenteredSteps.State rs)
    (ctx : GeneralNominalCandidates.Context) (p : Plan rs) : GeneralNominalCenteredSteps.State rs :=
  { before with
    erased := { before.erased with current := { before.erased.current with
      context := ctx
      sites := before.erased.current.sites ++ (emitted p).map Site.observed
      edges := before.erased.current.edges ++ (children p).map (fun d => (p.packet.site.occurrence,d)) } }
    sites := before.sites ++ emitted p
    sourceRecorded := fun s h => List.mem_append_left _ (before.sourceRecorded s h) }

structure Journal (rs : Roles.RoleDecls) where
  mixed : State rs
  versionedWhere : List (Plan rs)

def install (j : Journal rs) (ctx : GeneralNominalCandidates.Context) (p : Plan rs) : Journal rs :=
  ⟨⟨⟨installCore j.mixed.core ctx p,j.mixed.legacy.effects⟩,j.mixed.plans,j.mixed.effects⟩,
    j.versionedWhere ++ [p]⟩

def Models (j : Journal rs) (m : Assignment) : Prop :=
  GeneralNominalVersionedJournal232.Models j.mixed m ∧
    ∀ p ∈ j.versionedWhere, Holds p m ∧
      GeneralNominalVersionedEffects231.ClassEffects j.mixed.core p.packet.site.occurrence p m

/-- The new transaction uses the real pre-install frame and ordinary
selection. Availability of a common post-install model is required; no
resolver is claimed to compute or schedule this transition. -/
inductive InstallStep (r : Registry) : Journal rs → Journal rs → Prop where
  | whereRow (ctx : GeneralNominalCandidates.Context) (p : Plan rs) :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary rs).Checked r →
    Frame (Compiled r) before.mixed.core p.packet.site.occurrence p.packet.declaration.id p →
    GeneralNominalVersionedMixedSourceBoundary234.Local r before.mixed p.packet.site.occurrence
      (.selected p.packet.declaration.id (GeneralNominalVersionedFrame231.children p.packet)) →
    GeneralNominalCycleSteps.ChoiceCompatible before.mixed.core.erased.current p.packet →
    GeneralNominalRefinements.Refines before.mixed.core.erased.current.context.state ctx.state →
    ctx.interpretation = before.mixed.core.erased.current.context.interpretation →
    (∃ m, Models before m ∧ Models (install before ctx p) m) →
    InstallStep r before (install before ctx p)

theorem fixture_emitted : emitted rootPlan = [site] := by
  have length := congrArg List.length (ordered rootPlan)
  rw [GeneralWhereVersionCase317.ordered_children] at length
  simp only [List.length_map,List.length_singleton] at length
  obtain ⟨one,eq⟩ := List.length_eq_one_iff.mp length
  have member : one ∈ emitted rootPlan := eq ▸ List.mem_singleton_self _
  obtain ⟨clause,_,same⟩ := List.mem_map.mp member
  have visible := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
  have named : clause.val = otherChild := List.mem_singleton.mp visible
  have sameSite : one = site := by
    rw [← same]
    rcases clause with ⟨clause,valid⟩
    change clause = otherChild at named
    subst clause
    rfl
  exact eq.trans (congrArg List.singleton sameSite)

noncomputable abbrev before : Journal roles := ⟨after,[]⟩
noncomputable abbrev fixed : Journal roles := install before context rootPlan

theorem mixed_eq : fixed.mixed = framedState := by
  change (install before context rootPlan).mixed = framedState
  unfold install installCore framedState core
  simp only [fixture_emitted,List.map_cons,List.map_nil]
  rfl

theorem current_classes (m : Assignment) (valid : ParentHolds m) :
    GeneralNominalVersionedEffects231.ClassEffects core root rootPlan m := by
  exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
    (fun out => GeneralWhereVersionCommit317.requests_iff root out)).mpr valid.2.2.2.1

theorem models (m : Assignment) (valid : ParentHolds m) : Models fixed m := by
  refine ⟨mixed_eq.symm ▸ compiled_models m valid,?_⟩
  intro p member
  change p ∈ [rootPlan] at member
  cases List.mem_singleton.mp member
  rw [mixed_eq]
  exact ⟨GeneralWhereVersionSemantics317.full m valid,current_classes m valid⟩

theorem step : InstallStep sourceRegistry before fixed := by
  apply InstallStep.whereRow context rootPlan boundary_checked frame
  · rw [GeneralLiveCompoundPostRootHead316.root_children]
    exact selected
  · exact GeneralLiveCompoundProposedRepair316.choice_compatible
  · exact GeneralWhereVersionRefine317.refines
  · rfl
  · obtain ⟨m,valid⟩ := GeneralWhereVersionWitness317.inhabited
    exact ⟨m,⟨valid.1,by intro _ none; cases none⟩,models m valid⟩

theorem from_every_before (m : Assignment) (legal : Models before m) :
    ∃ n, Models before n ∧ Models fixed n ∧ ParentHolds n := by
  obtain ⟨n,ok⟩ := GeneralWhereVersionWitness317.model_from_each m legal.1
  exact ⟨n,⟨ok.1,by intro _ none; cases none⟩,models n ok,ok⟩

end Yulang.GeneralWhereVersionInstall317
