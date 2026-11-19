import Yulang.GeneralRebaseInstallDeltaModels279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseInstallNovelty279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedChildren232 (edges edge_iff)
open GeneralNominalVersionedMixedKernel234 (Committed Installable At Step)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalSaturationState (Generated)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseInstallDeltaModels279 (Delta NoFreshRequests models_iff no_fresh_iff)

variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
abbrev Edge (roles : Roles.RoleDecls) := Occurrence roles × Occurrence roles

def Covered (state : State roles) (plan : Plan roles) : Prop :=
  ∀ child ∈ children plan.packet,
    (plan.packet.site.occurrence,child) ∈ state.core.erased.current.edges

def FreshChild (state : State roles) (plan : Plan roles) : Prop :=
  ∃ child ∈ children plan.packet,
    (plan.packet.site.occurrence,child) ∉ state.core.erased.current.edges

def FullSilent (state : State roles) (effect : Effect roles) : Prop :=
  ∀ m, Models (install state effect) m ↔ Models state m

def LostModel (state : State roles) (effect : Effect roles) : Prop :=
  ∃ m, Models state m ∧ ¬ Models (install state effect) m

theorem silence_iff (snapshot : effect.snapshot = state.core) :
    FullSilent state effect ↔
      (∀ m, Models state m →
        GeneralNominalVersionedPlans231.Holds effect.plan m ∧
        GeneralNominalVersionedEffects231.ClassEffects state.core effect.plan.packet.site.occurrence effect.plan m) ∧
      (∀ m, Models state m → Delta state effect m) := by
  constructor
  · intro h
    exact ⟨fun m old =>
      let h' := (models_iff snapshot m).mp ((h m).mpr old)
      ⟨h'.2.1,h'.2.2.1⟩,
      fun m old => ((models_iff snapshot m).mp ((h m).mpr old)).2.2.2⟩
  · rintro ⟨holds,delta⟩ m
    rw [models_iff snapshot m]
    exact ⟨And.left,fun old => ⟨old,(holds m old).1,(holds m old).2,delta m old⟩⟩

theorem no_loss_iff (snapshot : effect.snapshot = state.core) :
    FullSilent state effect ↔ ¬ LostModel state effect := by
  classical
  constructor
  · rintro same ⟨m,old,lost⟩
    exact lost ((same m).mpr old)
  · intro none m
    refine ⟨GeneralNominalVersionedInstall232.step_models snapshot,?_⟩
    intro old
    by_cases new : Models (install state effect) m
    · exact new
    · exact False.elim (none ⟨m,old,new⟩)

theorem edge_exact (state : State roles) (effect : Effect roles) (edge : Edge roles) :
    edge ∈ (install state effect).core.erased.current.edges ∧
      edge ∉ state.core.erased.current.edges ↔
    edge ∈ edges effect.plan ∧ edge ∉ state.core.erased.current.edges := by
  classical
  change (edge ∈ state.core.erased.current.edges ++ edges effect.plan ∧ _) ↔ _
  rw [List.mem_append]
  by_cases old : edge ∈ state.core.erased.current.edges <;> simp [old]

theorem fresh_iff_edge (state : State roles) (effect : Effect roles) :
    FreshChild state effect.plan ↔ ∃ edge : Edge roles,
      edge ∈ (install state effect).core.erased.current.edges ∧ edge ∉ state.core.erased.current.edges := by
  constructor
  · rintro ⟨kid,mem,novel⟩
    exact ⟨_,(edge_exact state effect _).mpr ⟨GeneralNominalVersionedChildren232.child_edge mem,novel⟩⟩
  · rintro ⟨edge,new⟩
    obtain ⟨added,novel⟩ := (edge_exact state effect edge).mp new
    obtain ⟨kid,mem,rfl⟩ := edge_iff.mp added
    exact ⟨kid,mem,novel⟩

theorem not_covered (state : State roles) (plan : Plan roles) :
    ¬ Covered state plan ↔ FreshChild state plan := by
  classical
  constructor
  · intro fails
    by_cases some : FreshChild state plan
    · exact some
    · exfalso
      apply fails
      intro child mem
      by_cases old : (plan.packet.site.occurrence,child) ∈ state.core.erased.current.edges
      · exact old
      · exact False.elim (some ⟨child,mem,old⟩)
  · rintro ⟨child,mem,novel⟩ covered
    exact novel (covered child mem)

theorem committed_of_silent (snapshot : effect.snapshot = state.core)
    (same : FullSilent state effect) (closed : Covered state effect.plan) :
    Committed state effect.plan :=
  ⟨((silence_iff snapshot).mp same).1,closed⟩

theorem preservation_iff (snapshot : effect.snapshot = state.core) :
    FullSilent state effect ∧ Covered state effect.plan ↔
      Committed state effect.plan ∧ (∀ m, Models state m → Delta state effect m) := by
  rw [silence_iff snapshot]
  constructor
  · rintro ⟨⟨held, delta⟩, covered⟩
    exact ⟨⟨held,covered⟩,delta⟩
  · rintro ⟨⟨held,covered⟩,delta⟩
    exact ⟨⟨held,delta⟩,covered⟩

theorem novel_child_blocks (novel : FreshChild state effect.plan) :
    ¬ Committed state effect.plan := fun done => ((not_covered state effect.plan).mpr novel) done.2

/-- An actual raw installation rejected by neither guard either drops a full
model or adds a new child edge. In particular agreement of public projections
cannot be substituted for the full-model comparison. -/
theorem install_dichotomy (snapshot : effect.snapshot = state.core)
    (notDone : ¬ Committed state effect.plan) : LostModel state effect ∨ FreshChild state effect.plan := by
  classical
  by_cases lost : LostModel state effect
  · exact .inl lost
  · exact .inr ((not_covered state effect.plan).mp
      (fun closed => notDone (committed_of_silent snapshot ((no_loss_iff snapshot).mpr lost) closed)))

theorem graph_only (snapshot : effect.snapshot = state.core) (same : FullSilent state effect) :
    ¬ Committed state effect.plan ↔ FreshChild state effect.plan := by
  constructor
  · intro notDone
    exact ((install_dichotomy snapshot notDone).resolve_left ((no_loss_iff snapshot).mp same))
  · exact novel_child_blocks

theorem graph_step {registry : Registry} {root : Occurrence roles}
    (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (enabled : Installable registry state effect)
    (novel : FreshChild state effect.plan) : Step registry root state (install state effect) :=
  ⟨_,generated,.install effect enabled (novel_child_blocks novel)⟩

theorem graph_growth {root child : Occurrence roles}
    (generated : Generated state.core.erased.current root effect.plan.packet.site.occurrence)
    (member : child ∈ children effect.plan.packet) :
    Generated (install state effect).core.erased.current root child :=
  .child (GeneralNominalVersionedInstallProperties232.generated_preserved generated)
    (GeneralNominalVersionedInstall232.installed_child member)

end Yulang.GeneralRebaseInstallNovelty279
