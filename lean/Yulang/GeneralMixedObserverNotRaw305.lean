import Yulang.GeneralMixedTaggedEarlyRefresh305
import Yulang.GeneralRebaseDepthPathSelection285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31500
set_option maxHeartbeats 18000000
namespace Yulang.GeneralMixedObserverNotRaw305
open GeneralDictionaryOutputDepth252 (registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralMixedTaggedEarlyRefresh305 (middle first_actual second_actual)
open GeneralMixedReindexOutputFixture305 (widened)
open GeneralMixedReindexOutputHalt305 (widened_halted)
open GeneralMixedRawSchedule305 (lengths_realized)
open GeneralMixedReindexOutputCompiler305 (bits complete actual_run)
open GeneralMixedDiagnosticHead304 (boundary8)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralRebaseDepthPathRank285 (ActualPath all_after_install)
open GeneralRebaseDiagnosticData268 (Valid)
open GeneralRebaseDiagnosticV8268 (run)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)

theorem valid_on_any_prefix {s : State roles} {n : Nat} (trace : ActualPath installed s n) :
    Valid (boundary8 roles) registry s root bits := by
  have picked := GeneralNominalVersionedMixedBoundary234.local_iff.mp
    (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp
      (GeneralRebaseDepthPathSelection285.selected trace))
  have ⟨middle,sharing⟩ := B4TargetV8.selected_iff.mp picked
  have ⟨last,merged⟩ := B4TargetV7.selected_iff.mp middle
  cases last with
  | selected safe unique outputs =>
    refine ⟨safe.1,safe.2.1,safe.2.2.1,safe.2.2.2,unique,?_,merged,sharing⟩
    intro key
    change GeneralRebasePartialBool268.Reflect _ (if key = 0 then some false else none)
    split
    · rename_i zero
      subst key
      exact outputs
    · trivial

theorem exact_on_any_prefix {s : State roles} {n : Nat} (trace : ActualPath installed s n)
    (f : CommonRoleOutermostResolver.Frontier (GeneralSourceDictionaries.Occurrence roles)) :
    run bits = some f ↔ B4TargetV8.Local (boundary8 roles) registry s root f :=
  GeneralRebaseDiagnosticV8268.exact_of_complete (boundary8 roles) registry s root bits
    (valid_on_any_prefix trace) complete f

theorem observed_prefixes {s t : State roles} {n m : Nat}
    (p : ActualPath installed s n) (q : ActualPath installed t m) :
    (∀ f, B4TargetV8.Local (boundary8 roles) registry s root f ↔
      B4TargetV8.Local (boundary8 roles) registry t root f) ∧
    (∀ a, Models s a ↔ Models t a) ∧
    (∀ a payload, Models s a ∧ Evidence registry s.core a root payload ↔
      Models t a ∧ Evidence registry t.core a root payload) :=
  ⟨fun f => (exact_on_any_prefix p f).symm.trans (exact_on_any_prefix q f),
   fun a => ((all_after_install p).2 a).trans ((all_after_install q).2 a).symm,
   fun a payload => (GeneralRebaseDepthPathEvidence285.query p a payload).trans
      (GeneralRebaseDepthPathEvidence285.query q a payload).symm⟩

theorem different_step_availability :
    ∃ can cannot : State roles,
      (∀ f, B4TargetV8.Local (boundary8 roles) registry can root f ↔
        B4TargetV8.Local (boundary8 roles) registry cannot root f) ∧
      (∀ m : Assignment, Models can m ↔ Models cannot m) ∧
      (∀ (m : Assignment) (p : Payload), Models can m ∧ Evidence registry can.core m root p ↔
        Models cannot m ∧ Evidence registry cannot.core m root p) ∧
      Step registry root can cannot ∧ (∀ next, ¬ Step registry root cannot next) := by
  have a : ActualPath installed (middle 0 0) 1 := .more (.empty _) (first_actual 0 0)
  have b := (lengths_realized 1).1
  obtain ⟨diag,models,evidence⟩ := observed_prefixes a b
  exact ⟨middle 0 0,widened 1,diag,models,evidence,
    second_actual 0 1 (by decide) 0 1,widened_halted 1⟩

end Yulang.GeneralMixedObserverNotRaw305
