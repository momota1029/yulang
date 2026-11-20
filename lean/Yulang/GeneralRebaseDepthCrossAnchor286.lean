import Yulang.GeneralRebaseDepthPreInstall286

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14000000
namespace Yulang.GeneralRebaseDepthCrossAnchor286
open GeneralDictionaryOutputDepth252 (roles root registry plan declaration model)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthPreAnchor286 (Anchor)
open GeneralRebaseDepthPrePlan286 (Certified Kept)
open GeneralRebaseDepthPreInstall286 (installed_uses_certified installed_check)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralRebaseDepthPathAnchor285 (PublicModels snapshot)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_refl subtype_trans)

theorem output_equality_closed {t : State roles} (same : PublicModels t)
    (raw : ∀ m, GeneralNominalState.Models (snapshot t) m ↔ InitialTypeCheck m) :
    GeneralNominalVersionedMixedTerminalStable234.EqualityClosed t := by
  intro a b _ _ equal
  by_cases sameId : a = b
  · subst b
    intro m _
    exact ⟨subtype_refl _,subtype_refl _⟩
  have transported : GeneralNominalVersionedMixedKernel234.Equal
      GeneralRebaseDepthScalar285.refreshed a b :=
    fun m checked => equal m ((same m).mpr ((GeneralRebaseDepthScalar285.fixed_models m).mp checked))
  by_cases highA : 3 < a
  · exact (GeneralRebaseDepthTerminalFrame285.isolate_high a b highA sameId transported).elim
  by_cases highB : 3 < b
  · exact (GeneralRebaseDepthTerminalFrame285.isolate_high b a highB (Ne.symm sameId)
      (fun m yes => ⟨(transported m yes).2,(transported m yes).1⟩)).elim
  have full := transported model ((GeneralRebaseDepthScalar285.fixed_models model).mpr
    GeneralDictionaryOutputDepthInstall252.installed_model)
  rw [GeneralRebaseDepthTerminalFrame285.literal_depth a,GeneralRebaseDepthTerminalFrame285.literal_depth b] at full
  obtain eq | low := GeneralRebaseDepthTerminalFrame285.zero_one a b
    ((GeneralNominalOutputGrowth.tower_equivalent _ _).mp full) (by omega) (by omega)
  · exact (sameId eq).elim
  · intro m valid
    have source := (raw m).mp valid
    have scalar (n : Nat) (small : n ≤ 1) :
        Equivalent (m n).1 GeneralDictionaryOutputDepth252.S := by
      have eq : n = 0 ∨ n = 1 := by omega
      rcases eq with rfl|rfl
      · exact source.1
      · exact source.2.1
    have first := scalar a low.1
    have last := scalar b low.2
    exact ⟨subtype_trans first.1 last.2,subtype_trans last.1 first.2⟩

theorem raw_check {s : State roles} (a : Anchor s) {e : Effect roles} (v : Certified s e.plan)
    (m : Assignment) : GeneralNominalState.Models (snapshot (install s e)) m ↔ InitialTypeCheck m := by
  change GeneralNominalState.Models (replayPlan e.plan).packet.context.state m ↔ _
  rw [GeneralNominalVersionedInstallation231.replay_private_models,
    GeneralNominalVersionedPlans231.private_models_iff,v.frame.context_eq]
  exact ⟨fun valid => (a.rawModels m).mp valid.1,
    fun checked => ⟨(a.rawModels m).mpr checked,(v.inputs m).1⟩⟩

theorem nominal_retained {s : State roles} (a : Anchor s) {e : Effect roles} (v : Certified s e.plan) :
    ∃ slot, (snapshot (install s e)).base.source slot = 2 ∧
      ∃ d, (snapshot (install s e)).nominals slot = some d := by
  change ∃ slot, e.plan.packet.context.state.base.source slot = 2 ∧
    ∃ d, e.plan.packet.context.state.nominals slot = some d
  rw [v.frame.context_eq]
  exact a.nominalTwo

theorem points_retained {s : State roles} (a : Anchor s) {e : Effect roles} (v : Certified s e.plan) :
    GeneralNominalReobservationSteps.PointClosed (snapshot (install s e)) := by
  change GeneralNominalReobservationSteps.PointClosed e.plan.packet.context.state
  rw [v.frame.context_eq]
  exact a.point

theorem empty_emissions {s : State roles} {p : GeneralNominalCenters.Plan roles} (v : Certified s p) :
    GeneralNominalVersionedChildren232.emitted p = [] := by
  unfold GeneralNominalVersionedChildren232.emitted
  have no : p.packet.declaration.requirements = [] := by
    rw [List.mem_singleton.mp v.frame.visible]
    rfl
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro site member
  obtain ⟨clause,_,_⟩ := List.mem_map.mp member
  have none : clause.val ∈ ([] : List GeneralDeclarations.Clause) := by
    simpa only [GeneralCanonicalChildOrder.canonicalRequirements,no,List.mergeSort_nil] using clause.property
  cases none

theorem anchored {s : State roles} (a : Anchor s) (kept : Kept s) {e : Effect roles}
    (enabled : Installable registry s e) (atRoot : e.plan.packet.site.occurrence = root) :
    GeneralRebaseDepthPathAnchor285.Anchor (install s e) := by
  have v := installed_uses_certified a kept enabled atRoot
  have meaning := installed_check a kept enabled atRoot
  refine ⟨meaning,nominal_retained a v,points_retained a v,
    output_equality_closed meaning (raw_check a v),?_,?_,?_⟩
  · change s.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites e.plan = _
    unfold GeneralNominalVersionedChildren232.rawSites
    rw [empty_emissions v,List.map_nil,List.append_nil]
    exact a.sites
  · change s.core.sites ++ GeneralNominalVersionedChildren232.emitted e.plan = _
    rw [empty_emissions v,List.append_nil]
    exact a.centers
  · change s.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges e.plan = _
    unfold GeneralNominalVersionedChildren232.edges
    rw [v.leaf,List.map_nil,List.append_nil]
    exact a.edges

theorem aliases {s : State roles} (a : Anchor s) (e : Effect roles) :
    (install s e).core.erased.current.aliases = [] := a.aliases

theorem known_iff {s : State roles} {e : Effect roles} (v : Certified s e.plan) (n : Nat) :
    GeneralNominalState.Known (snapshot (install s e)) n ↔ GeneralNominalState.Known (snapshot s) n := by
  change GeneralNominalState.Known (replayPlan e.plan).packet.context.state n ↔ _
  rw [GeneralNominalVersionedInstallation231.replay_known,v.frame.context_eq]

end Yulang.GeneralRebaseDepthCrossAnchor286
