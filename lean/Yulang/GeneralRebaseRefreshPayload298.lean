import Yulang.GeneralRebaseRefreshInstall298
import Yulang.GeneralRebaseRevisitedTrace298

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseRefreshPayload298
open GeneralDictionaryOutputDepth252 (roles registry sourceRegistry root declaration initial plan children_empty reachable)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseSignedDepth297 (checked)
open GeneralRebasePreInstallReplay297 (after candidate)
open GeneralRebaseRefreshInstall298 (actual_effect exact_two_steps)
open GeneralRebaseOutputDepthSuccessor271 (owner output)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Effect State Models)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Installable Committed)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralDictionaryReadback (Payload payload_iff_erased)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseRevisitedTrace298 (Family Trace)
open GeneralRebaseSourceSurvivor267 (Boundary)

theorem has_leaf {e : Effect roles} (same : e.plan = candidate)
    (enabled : Installable registry after e) (a : Assignment) (valid : Models (install after e) a) :
    Evidence registry (install after e).core a root (.node 0 []) := by
  have leaves : GeneralNominalVersionedFrame231.children e.plan.packet = [] := by
    rw [same]
    exact (GeneralRebaseNonleafRetarget276.children_eq plan
      (GeneralRebaseSignedRefresh297.refinement GeneralRebasePreInstallReplay297.cert rfl)
      (GeneralRebaseSignedRefresh297.interp GeneralRebasePreInstallReplay297.cert rfl)
      GeneralRebasePreInstallReplay297.seen).trans children_empty
  have witnessed := GeneralNominalVersionedInstalledEvidence233.evidence enabled.snapshot_eq leaves valid
  rw [enabled.registry_eq,same] at witnessed
  exact witnessed

theorem only_leaf (s : State roles) (a : Assignment) (p : Payload)
    (ev : Evidence registry s.core a root p) : p = .node 0 [] := by
  have rendered := (payload_iff_erased _ _ _).mpr ev
  cases rendered with
  | node rule kids =>
    obtain ⟨c,cert⟩ := rule
    have decl : c.packet.declaration = declaration := List.mem_singleton.mp cert.frame.visible
    have key := cert.frame.key_eq
    rw [decl] at key
    have empty : GeneralNominalVersionedFrame231.children c.packet = [] := by
      unfold GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
      simp only [GeneralCanonicalChildOrder.canonicalEmit,decl,
        show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration by decide +kernel]
      rfl
    rw [cert.children_eq,empty] at kids
    cases kids
    exact congrArg (fun k => CommonRoleOutermostResolver.Dictionary.node k []) key.symm

theorem same_models_and_payload {e : Effect roles} (same : e.plan = candidate)
    (enabled : Installable registry after e) (a : Assignment) (p : Payload) :
    Models (install after e) a ∧ Evidence registry (install after e).core a root p ↔
    Models installed a ∧ Evidence registry installed.core a root p := by
  have eqM := GeneralRebaseRefreshInstall298.models_same same enabled a
  constructor
  · intro held
    have model := eqM.mp held.1
    exact ⟨model,(GeneralRebaseDepthPayload285.evidence_exact a model p).mpr
      (only_leaf _ a p held.2)⟩
  · intro held
    have agrees := (GeneralRebaseDepthPayload285.evidence_exact a held.1 p).mp held.2
    subst p
    have model := eqM.mpr held.1
    exact ⟨model,has_leaf same enabled a model⟩

theorem actual_annotated (codes : Family sourceRegistry root checked) :
    ∃ e : Effect roles, ∃ p, e.plan = candidate ∧
      Trace codes [owner] [output] initial (install after e) [p] ∧
      (∀ m d, Models (install after e) m ∧ Evidence registry (install after e).core m root d ↔
        Models installed m ∧ Evidence registry installed.core m root d) := by
  obtain ⟨e,same,enabled,fresh⟩ := actual_effect
  have step := GeneralRebaseRefreshInstall298.real_step same enabled fresh
  have prior := GeneralRebaseRefreshInstall298.before_projection
  have next := GeneralRebaseRefreshInstall298.project_same same enabled
  have different : project [owner] [output] after ≠ project [owner] [output] (install after e) := by
    rw [←prior,next,GeneralRebaseOutputDepthSuccessor271.initial_view]
    intro eq
    have contradictionValue := congrArg GeneralRebaseStep258.State.remaining eq
    rw [GeneralRebaseOutputDepthSuccessor271.projected_install] at contradictionValue
    exact (by decide +kernel : GeneralRebaseOutputDepthSuccessor271.support ≠ []) contradictionValue
  obtain ⟨p,listed,wrote⟩ := GeneralRebaseLocalProgram298.represents
    GeneralRebasePreInstallReplay297.source_reachable (codes after) [owner] [output] step (Ne.symm different)
  have pause : Trace codes [owner] [output] initial after [] :=
    .silent (.nil _) GeneralRebasePreInstallReplay297.actual_before_install prior
  exact ⟨e,p,same,.strict pause step different listed wrote,same_models_and_payload same enabled⟩

end Yulang.GeneralRebaseRefreshPayload298
