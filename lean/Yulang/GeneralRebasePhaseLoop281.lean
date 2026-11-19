import Yulang.GeneralRebasePhaseFixture281

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebasePhaseLoop281
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebasePhaseMachine281 (Step)
open GeneralRebasePhaseKeys281 (Codec Added Seen owner fresh_iff)
open GeneralRebaseChartSilent281 (oldChart looseChart)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseChartStep281 (Chart quiet_kept)

def onceCodec (roles : Roles.RoleDecls) : Codec roles Unit :=
  ⟨[()],fun _ => some (),fun _ _ _ => List.mem_cons_self⟩

def oldEmpty : Chart Unit Assignment := oldChart [] (fun _ _ => True)
def looseEmpty : Chart Unit Assignment := looseChart [] (fun _ _ => True)

namespace Version
open GeneralDictionaryVersionLoopSource237 (roles registry sourceRegistry root initial)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (plan)
open GeneralRebaseVersionMicro278 (installed refreshed install_step refresh_step reobserve_step)
open GeneralRebaseInstallPublicObstruction279.Version (e)

theorem key_constant (n : Nat) : owner (plan n) = owner (plan 0) := rfl

theorem no_previous : ¬ Seen (onceCodec roles) initial (owner (plan 0),()) := by
  rintro ⟨p,recorded,_,_⟩
  cases recorded

theorem first_install : Step oldEmpty (onceCodec roles) sourceRegistry root initial (installed 0) := by
  apply GeneralRebasePhaseMachine281.phase_kept (GeneralRebaseChartSilent281.Version.preserved_raw 0)
  exact (fresh_iff (effect := e 0) (onceCodec roles)).mpr ⟨(),rfl,no_previous⟩

theorem first_round : B4Target.Steps (Step oldEmpty (onceCodec roles) sourceRegistry root) initial (state 1) :=
  .tail (.tail (.tail .refl first_install) (Or.inl (quiet_kept (refresh_step 0) rfl)))
    (Or.inl (quiet_kept (reobserve_step 0) rfl))

theorem phase_seen (n : Nat) : Seen (onceCodec roles) (state (n+1)) (owner (plan (n+1)),()) :=
  ⟨plan 0,(stages (n+1)).recorded 0 (by omega),(key_constant (n+1)).symm,rfl⟩

theorem no_repeat (n : Nat) :
    ¬ Step oldEmpty (onceCodec roles) sourceRegistry root (state (n+1)) (installed (n+1)) := by
  intro maybe
  have phase := GeneralRebasePhaseMachine281.ledger_only maybe
    (GeneralRebaseChartSilent281.Version.blocked_every [] (fun _ _ => True) (n+1))
  obtain ⟨⟨⟩,_,missing⟩ := (fresh_iff (effect := e (n+1)) (onceCodec roles)).mp phase
  exact missing (phase_seen n)

end Version

namespace Loose
open GeneralDictionaryLooseLoopSource240 (roles registry sourceRegistry root initial)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseIterationBook240 (plan)
open GeneralRebaseLooseMicro278 (installed refreshed actual)
open GeneralRebaseInstallPublicObstruction279.Loose (e)

theorem key_constant (n : Nat) : owner (plan n) = owner (plan 0) := rfl

theorem no_previous : ¬ Seen (onceCodec roles) initial (owner (plan 0),()) := by
  rintro ⟨p,recorded,_,_⟩
  cases recorded

theorem first_install : Step looseEmpty (onceCodec roles) sourceRegistry root initial (installed 0) := by
  apply GeneralRebasePhaseMachine281.phase_kept (GeneralRebaseChartSilent281.Loose.preserved_raw 0)
  exact (fresh_iff (effect := e 0) (onceCodec roles)).mpr ⟨(),rfl,no_previous⟩

theorem first_round : B4Target.Steps (Step looseEmpty (onceCodec roles) sourceRegistry root) initial (state 1) :=
  .tail (.tail (.tail .refl first_install) (Or.inl (quiet_kept (actual ⟨0,.installed⟩) rfl)))
    (Or.inl (quiet_kept (actual ⟨0,.refreshed⟩) rfl))

theorem phase_seen (n : Nat) : Seen (onceCodec roles) (state (n+1)) (owner (plan (n+1)),()) :=
  ⟨plan 0,(stages (n+1)).recorded 0 (by omega),(key_constant (n+1)).symm,rfl⟩

theorem no_repeat (n : Nat) :
    ¬ Step looseEmpty (onceCodec roles) sourceRegistry root (state (n+1)) (installed (n+1)) := by
  intro maybe
  have phase := GeneralRebasePhaseMachine281.ledger_only maybe
    (GeneralRebaseChartSilent281.Loose.blocked_every [] (fun _ _ => True) (n+1))
  obtain ⟨⟨⟩,_,missing⟩ := (fresh_iff (effect := e (n+1)) (onceCodec roles)).mp phase
  exact missing (phase_seen n)

end Loose
end Yulang.GeneralRebasePhaseLoop281
