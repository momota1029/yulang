import Yulang.GeneralRebaseEdgeReceipt279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompactEdgeInstall279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralRebaseEdgeReceipt279 (receipt append_delta_membership)
open GeneralNominalSaturationState (Alias Generated)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedFrameTransport232 (class_effects_iff frame_forward instance_forward)
open GeneralNominalVersionedMixedKernel234 (Committed)

def replaceEdges (state : State roles) (new : List (Edge roles)) : State roles :=
  {state with legacy := {state.legacy with core := {state.core with erased :=
    {state.core.erased with current := {state.core.erased.current with edges := new} } } } }

theorem requests_exact (state : State roles) (new : List (Edge roles)) (root : Occurrence roles)
    (output : GeneralSourceState.Output) :
    output ∈ requests (replaceEdges state new).core root ↔ output ∈ requests state.core root :=
  GeneralNominalVersionedRefresh232.requests_iff_of_same_lists rfl rfl

theorem classes_exact (state : State roles) (new : List (Edge roles)) (root : Occurrence roles)
    (plan : Plan roles) (m : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects (replaceEdges state new).core root plan m ↔
    GeneralNominalVersionedEffects231.ClassEffects state.core root plan m :=
  class_effects_iff (requests_exact state new root)

theorem legacy_models_exact (state : State roles) (new : List (Edge roles)) (m : Assignment) :
    GeneralNominalVersionedJournal232.Legacy.Models (replaceEdges state new).legacy m ↔
    GeneralNominalVersionedJournal232.Legacy.Models state.legacy m := by
  constructor <;> intro valid
  · refine ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
    intro eff present
    have h := valid.2.2.2.2.2 eff present
    exact ⟨h.1,(GeneralNominalVersionedEffects231.class_effects_iff ..).mp
      ((classes_exact state new _ eff.plan m).mp
        ((GeneralNominalVersionedEffects231.class_effects_iff ..).mpr h.2))⟩
  · refine ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
    intro eff present
    have h := valid.2.2.2.2.2 eff present
    exact ⟨h.1,(GeneralNominalVersionedEffects231.class_effects_iff ..).mp
      ((classes_exact state new _ eff.plan m).mpr
        ((GeneralNominalVersionedEffects231.class_effects_iff ..).mpr h.2))⟩

theorem models_exact (state : State roles) (new : List (Edge roles)) (m : Assignment) :
    Models (replaceEdges state new) m ↔ Models state m := by
  constructor <;> intro valid
  · refine ⟨(legacy_models_exact state new m).mp valid.1,valid.2.1,?_⟩
    intro eff present
    have h := valid.2.2 eff present
    exact ⟨h.1,(classes_exact state new _ _ m).mp h.2⟩
  · refine ⟨(legacy_models_exact state new m).mpr valid.1,valid.2.1,?_⟩
    intro eff present
    have h := valid.2.2 eff present
    exact ⟨h.1,(classes_exact state new _ _ m).mpr h.2⟩

theorem aliases_exact (state : State roles) (new : List (Edge roles)) (first last : Nat) :
    Alias (replaceEdges state new).core.erased.current first last ↔
      Alias state.core.erased.current first last := by
  constructor <;> intro h <;> induction h with
  | refl => exact .refl _
  | edge member => exact .edge member
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem generated_exact (state : State roles) (new : List (Edge roles))
    (same : ∀ edge, edge ∈ new ↔ edge ∈ state.core.erased.current.edges) (root focus : Occurrence roles) :
    Generated (replaceEdges state new).core.erased.current root focus ↔ Generated state.core.erased.current root focus := by
  constructor <;> intro h
  · induction h with
    | root => exact .root
    | child _ edge ih => exact .child ih ((same _).mp edge)
    | alias _ entered exited alias ih => exact .alias ih entered exited ((aliases_exact state new _ _).mp alias)
  · induction h with
    | root => exact .root
    | child _ edge ih => exact .child ih ((same _).mpr edge)
    | alias _ entered exited alias ih => exact .alias ih entered exited ((aliases_exact state new _ _).mpr alias)

theorem frame_exact (state : State roles) (new : List (Edge roles)) (registry : Registry)
    (root : Occurrence roles) (key : Nat) (plan : Plan roles) :
    GeneralNominalVersionedEvidence231.Frame registry (replaceEdges state new).core root key plan ↔
    GeneralNominalVersionedEvidence231.Frame registry state.core root key plan :=
  ⟨frame_forward rfl (fun _ h => h) (fun _ h => h),
    frame_forward rfl (fun _ h => h) (fun _ h => h)⟩

theorem evidence_exact (state : State roles) (new : List (Edge roles)) (registry : Registry)
    (root : Occurrence roles) (m : Assignment) (data : GeneralDictionaryReadback.Payload) :
    GeneralNominalVersionedEvidence231.Evidence registry (replaceEdges state new).core m root data ↔
    GeneralNominalVersionedEvidence231.Evidence registry state.core m root data := by
  constructor <;> rintro ⟨tree,rooted,old⟩
  · refine ⟨tree,rooted,?_⟩
    exact GeneralSourceDictionaries.evidence_mono _ _
      (fun _ _ _ h => instance_forward (before := (replaceEdges state new).core) (after := state.core) rfl (fun _ h => h) (fun _ h => h) h) old
  · refine ⟨tree,rooted,?_⟩
    exact GeneralSourceDictionaries.evidence_mono _ _
      (fun _ _ _ h => instance_forward (before := state.core) (after := (replaceEdges state new).core) rfl (fun _ h => h) (fun _ h => h) h) old

theorem committed_exact (state : State roles) (new : List (Edge roles))
    (same : ∀ edge, edge ∈ new ↔ edge ∈ state.core.erased.current.edges) (plan : Plan roles) :
    Committed (replaceEdges state new) plan ↔ Committed state plan := by
  constructor
  · rintro ⟨semantic,kids⟩
    exact ⟨fun m h =>
      let old := semantic m ((models_exact state new m).mpr h)
      ⟨old.1,(classes_exact state new _ _ m).mp old.2⟩,
      fun kid mem => (same _).mp (kids kid mem)⟩
  · rintro ⟨semantic,kids⟩
    exact ⟨fun m h =>
      let old := semantic m ((models_exact state new m).mp h)
      ⟨old.1,(classes_exact state new _ _ m).mpr old.2⟩,
      fun kid mem => (same _).mpr (kids kid mem)⟩

def reduced (state : State roles) (effect : Effect roles) : State roles :=
  replaceEdges (install state effect) (state.core.erased.current.edges ++ receipt state effect.plan)

theorem reduced_membership (state : State roles) (effect : Effect roles) (edge : Edge roles) :
    edge ∈ (reduced state effect).core.erased.current.edges ↔
    edge ∈ (install state effect).core.erased.current.edges :=
  append_delta_membership _ _ _

theorem reduced_models (state : State roles) (effect : Effect roles) (m : Assignment) :
    Models (reduced state effect) m ↔ Models (install state effect) m :=
  models_exact _ _ m

theorem reduced_generated (state : State roles) (effect : Effect roles) (root focus : Occurrence roles) :
    Generated (reduced state effect).core.erased.current root focus ↔
    Generated (install state effect).core.erased.current root focus :=
  generated_exact _ _ (reduced_membership state effect) root focus

theorem reduced_evidence (state : State roles) (effect : Effect roles) (registry : Registry)
    (root : Occurrence roles) (m : Assignment) (data : GeneralDictionaryReadback.Payload) :
    GeneralNominalVersionedEvidence231.Evidence registry (reduced state effect).core m root data ↔
    GeneralNominalVersionedEvidence231.Evidence registry (install state effect).core m root data :=
  evidence_exact _ _ registry root m data

end Yulang.GeneralRebaseCompactEdgeInstall279
