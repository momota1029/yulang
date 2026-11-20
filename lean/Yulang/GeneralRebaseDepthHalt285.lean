import Yulang.GeneralRebaseDepthCommit285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 11500000
namespace Yulang.GeneralRebaseDepthHalt285
open GeneralDictionaryOutputDepth252 (registry root plan roles initial)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthScalar285 (refreshed target actual_followup actual_silent_refresh fixed_models)
open GeneralRebaseDepthTerminalFrame285 (no_further_refresh equality_closed point_closed)
open GeneralRebaseDepthCommit285 (no_install raw_sites center_sites no_edges)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)

theorem halted (next : State roles) : ¬ Step registry root refreshed next := by
 rintro ⟨focus,generated,operation⟩
 have same := GeneralNominalVersionedMixedTerminalStable234.generated_only raw_sites no_edges generated
 cases operation with
 | administrative action =>
  cases action with
  | enqueue _ absent =>
    exact absent _ (raw_sites ▸ List.mem_singleton_self _) same.symm
  | refresh ctx cert identity present unknown known =>
    exact no_further_refresh ctx cert identity present unknown known
  | equate first last a b equal novel =>
    exact novel (equality_closed first last a b equal)
  | reobserve revision _ improves =>
    exact GeneralNominalReobservationSteps.pointClosed_no_revision (state := refreshed.core.erased.current) point_closed revision improves
 | refresh _ ctx cert identity present unknown known =>
  exact no_further_refresh ctx cert identity present unknown known
 | install effect enabled novel =>
  exact novel (no_install effect enabled same)
 | merge first last a b _ novel =>
  rw [center_sites] at a b
  cases List.mem_singleton.mp a
  cases List.mem_singleton.mp b
  exact novel (.refl _)

theorem stable : Stable registry refreshed root :=
 (GeneralNominalVersionedMixedKernel234.closure halted).1

theorem actual_reaches_halt :
    B4Target.Steps (Step registry root) initial refreshed ∧
      (∀ next, ¬ Step registry root refreshed next) ∧
      (∀ m, Models refreshed m ↔ Models installed m) :=
  ⟨actual_followup,halted,fixed_models⟩

theorem accessibility_at_endpoint :
    Acc (fun next prev => Step registry root prev next) refreshed :=
  .intro _ (fun next impossible => (halted next impossible).elim)

end Yulang.GeneralRebaseDepthHalt285
