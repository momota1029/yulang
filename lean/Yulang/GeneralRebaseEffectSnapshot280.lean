import Yulang.GeneralRebaseCompactAvailability279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseEffectSnapshot280
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalVersionedFrameTransport232 (class_effects_iff frame_forward)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges)
open GeneralNominalCenteredHeadOutputs (requests)

def coreAt (core : GeneralNominalCenteredSteps.State roles) (edges : List (Edge roles)) :
    GeneralNominalCenteredSteps.State roles :=
  {core with erased := {core.erased with current := {core.erased.current with edges := edges}}}

theorem core_twice (core : GeneralNominalCenteredSteps.State roles) (first last : List (Edge roles)) :
    coreAt (coreAt core first) last = coreAt core last := rfl

theorem core_self (core : GeneralNominalCenteredSteps.State roles) :
    coreAt core core.erased.current.edges = core := by
  cases core with
  | mk erased sites plans recorded known =>
    cases erased with
    | mk src state facts => cases state <;> rfl

theorem core_alias {core : GeneralNominalCenteredSteps.State roles} {edges : List (Edge roles)}
    (a b : Nat) :
    GeneralNominalSaturationState.Alias (coreAt core edges).erased.current a b ↔
    GeneralNominalSaturationState.Alias core.erased.current a b := by
  constructor <;> intro linked <;> induction linked with
  | refl => exact .refl _
  | edge stored => exact .edge stored
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem requests_iff (core : GeneralNominalCenteredSteps.State roles) (edges : List (Edge roles))
    (focus : Occurrence roles) (output : GeneralSourceState.Output) :
    output ∈ requests (coreAt core edges) focus ↔ output ∈ requests core focus :=
  GeneralNominalVersionedRefresh232.requests_iff_of_same_lists rfl rfl

def retag (eff : Effect roles) (edges : List (Edge roles)) : Effect roles :=
  ⟨eff.registry,coreAt eff.snapshot edges,eff.plan,
    frame_forward (before := eff.snapshot) (after := coreAt eff.snapshot edges) rfl (fun _ h => h) (fun _ h => h) eff.frame,eff.unique,
    fun output recorded => eff.ready output ((requests_iff _ _ _ _).mp recorded)⟩

theorem retag_twice (eff : Effect roles) (first last : List (Edge roles)) :
    retag (retag eff first) last = retag eff last := rfl

theorem retag_self (eff : Effect roles) : retag eff eff.snapshot.erased.current.edges = eff := by
  cases eff with
  | mk r core p h u ready =>
    cases core with
    | mk erased sites plans recorded known =>
      cases erased with
      | mk src state facts => cases state <;> rfl

theorem retag_holds (e : Effect roles) (edges : List (Edge roles)) (m : Assignment) :
    (retag e edges).Holds m ↔ e.Holds m := by
  exact and_congr Iff.rfl (class_effects_iff (requests_iff e.snapshot edges e.plan.packet.site.occurrence))

theorem retag_live (e : Effect roles) (edges : List (Edge roles))
    (core : GeneralNominalCenteredSteps.State roles) (m : Assignment) :
    (retag e edges).Live core m ↔ e.Live core m := Iff.rfl

def SameEdges (first last : List (Edge roles)) : Prop := ∀ e, e ∈ first ↔ e ∈ last

def EffectRelated (first last : Effect roles) : Prop :=
  ∃ edges, last = retag first edges ∧ SameEdges first.snapshot.erased.current.edges edges

theorem EffectRelated.refl (first : Effect roles) : EffectRelated first first :=
  ⟨first.snapshot.erased.current.edges,(retag_self first).symm,fun _ => Iff.rfl⟩

theorem EffectRelated.symm (related : EffectRelated first last) : EffectRelated last first := by
  obtain ⟨edges,rfl,same⟩ := related
  exact ⟨first.snapshot.erased.current.edges,(retag_twice ..).symm ▸ (retag_self first).symm,fun e => (same e).symm⟩

theorem EffectRelated.trans (a : EffectRelated first middle) (b : EffectRelated middle last) :
    EffectRelated first last := by
  obtain ⟨xs,rfl,one⟩ := a
  obtain ⟨ys,rfl,two⟩ := b
  exact ⟨ys,retag_twice ..,fun e => (one e).trans (two e)⟩

theorem EffectRelated.plan (related : EffectRelated a b) : a.plan = b.plan := by
  obtain ⟨_,rfl,_⟩ := related
  rfl

theorem EffectRelated.holds (related : EffectRelated a b) (m : Assignment) :
    a.Holds m ↔ b.Holds m := by
  obtain ⟨_,rfl,_⟩ := related
  exact (retag_holds ..).symm

theorem EffectRelated.live {a b : Effect roles} (related : EffectRelated a b) (core : GeneralNominalCenteredSteps.State roles)
    (m : Assignment) : a.Live core m ↔ b.Live core m := by
  obtain ⟨_,rfl,_⟩ := related
  exact (retag_live ..).symm

structure ArchiveRelated (first last : State roles) : Prop where
  legacy : first.legacy = last.legacy
  plans : first.plans = last.plans
  forward : ∀ e ∈ first.effects, ∃ other ∈ last.effects, EffectRelated e other
  backward : ∀ other ∈ last.effects, ∃ e ∈ first.effects, EffectRelated e other

theorem ArchiveRelated.core {a b : State roles} (same : ArchiveRelated a b) : a.core = b.core :=
  congrArg GeneralNominalCenteredHeadMatStepJournal.State.core same.legacy

theorem ArchiveRelated.symm {a b : State roles} (same : ArchiveRelated a b) : ArchiveRelated b a := by
  refine ⟨same.legacy.symm,same.plans.symm,?_,?_⟩
  · intro e h
    obtain ⟨other,member,rel⟩ := same.backward e h
    exact ⟨other,member,rel.symm⟩
  · intro e h
    obtain ⟨other,member,rel⟩ := same.forward e h
    exact ⟨other,member,rel.symm⟩

theorem ArchiveRelated.models {a b : State roles} (same : ArchiveRelated a b) (m : Assignment) :
    Models a m ↔ Models b m := by
  constructor
  · intro valid
    refine ⟨same.legacy ▸ valid.1,same.plans ▸ valid.2.1,?_⟩
    intro e recorded
    obtain ⟨old,member,related⟩ := same.backward e recorded
    have cert := valid.2.2 old member
    exact ⟨(related.holds m).mp cert.1,same.core ▸ (related.live a.core m).mp cert.2⟩
  · intro valid
    refine ⟨same.legacy.symm ▸ valid.1,same.plans.symm ▸ valid.2.1,?_⟩
    intro e recorded
    obtain ⟨new,member,related⟩ := same.forward e recorded
    have cert := valid.2.2 new member
    exact ⟨(related.holds m).mpr cert.1,same.core.symm ▸ (related.live b.core m).mpr cert.2⟩

end Yulang.GeneralRebaseEffectSnapshot280
