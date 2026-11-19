import Yulang.GeneralRebaseOptionalView282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseProspective282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedInstall232 (install InstallationModels install_models)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded entries same_entry)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty reachable_legacy_empty)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseHistoryOrder282 (history decode ordered)
open GeneralNominalRebaseJournalView243 (compile compile_exact)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralNominalOrderedRaw248 (read_mapping)
open GeneralPresenceDefinitionRewrite244 (Entry block)
open GeneralRebaseMixedOwnedTrace277 (raw)
open PresenceNormalForm (All)
open CommonNominalFullCarrier (model)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {before after : State roles} {effect : Effect roles}

theorem packet_context (snap : effect.snapshot = before.core) :
    effect.plan.packet.context = before.core.erased.current.context :=
  effect.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snap)

theorem installed_seed (snap : effect.snapshot = before.core) :
    (raw (install before effect)).seed = (raw before).seed := by
  change effect.plan.packet.context.state.seed = (raw before).seed
  exact congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.seed) (packet_context snap)

theorem recorded_install (same : Recorded before) (snap : effect.snapshot = before.core) :
    Recorded (install before effect) := by
  intro q listed
  rcases List.mem_cons.mp listed with rfl|prior
  · rfl
  · exact (same q prior).trans (installed_seed snap).symm

theorem empty_install (empty : LegacyEmpty before) : LegacyEmpty (install before effect) := empty

def Compiled (state : State roles) (base : Assignment) : Prop :=
  (compile state (mapping (history state))).Models base

theorem decoded {s : State roles} (empty : LegacyEmpty s) (m : Assignment) :
    Compiled s m ↔ Models s (decode s m) := by
  unfold Compiled decode
  rw [compile_exact s empty,read_mapping]

theorem members {s : State roles} (recorded : Recorded s) (entry : Entry Nat) :
    entry ∈ history s ↔ entry ∈ entries s :=
  ((ordered s).2.1.mem_iff (a := entry)).symm.trans
    ⟨fun h => GeneralPresenceOrderedDedup247.dedup_subset _ h,
      fun h => GeneralPresenceOrderedDedup247.member_preserved _ (fun _ hx _ hy eq => same_entry recorded hx hy eq) entry h⟩

theorem compile_old {s : State roles} (recorded : Recorded s) (empty : LegacyEmpty s)
    (m : Assignment) (valid : Models s m) : Compiled s m := by
  have writes : All model m (block (history s)) := by
    intro atom used
    obtain ⟨e,entry,inside⟩ := List.mem_flatMap.mp used
    exact GeneralNominalVersionedHistoryNormalization238.historical_equations valid e
      ((members recorded e).mp entry) atom inside
  have equivalent : GeneralNominalAssignmentCongruence238.Same (decode s m) m :=
    GeneralPresenceOrderedRecovery247.solve_compatible model GeneralPresenceCommonLaws245.common_laws _ _ writes
  exact (decoded empty m).mpr
    ((GeneralNominalVersionedSourceCongruence238.models_iff equivalent s empty).mpr valid)

theorem acceptance_before (reach : Reachable registry root before) (snap : effect.snapshot = before.core) :
    (∃ a, Compiled (install before effect) a) ↔ ∃ a, InstallationModels before effect a := by
  have empty := empty_install (effect := effect) (reachable_legacy_empty reach)
  have records := recorded_install (GeneralNominalVersionedMixedSeedLedger237.reachable reach) snap
  constructor
  · rintro ⟨a,valid⟩
    exact ⟨decode (install before effect) a,(install_models snap).mp ((decoded empty a).mp valid)⟩
  · rintro ⟨a,old⟩
    exact ⟨a,compile_old records empty a ((install_models snap).mpr old)⟩

end Yulang.GeneralRebaseProspective282
