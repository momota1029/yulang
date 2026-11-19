import Yulang.GeneralRebaseCompiledQuery282
import Yulang.GeneralDictionaryVersionLoopNontermination239
import Yulang.GeneralDictionaryLooseIterationNontermination240

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseCompiledRegressions282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseCompiledStep282 (Driver Guarded raw driver_exact guarded_exact guarded_raw)
open GeneralRebaseChartStep281 (Chart)
open GeneralRebasePhaseKeys281 (Codec)
open GeneralRebasePhaseMachine281 (Step)
open GeneralRebaseRoundMicro278 (Tick)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {start finish : State roles}

theorem acc_to_raw {s : State roles}
    (limited : Acc (fun after before => Driver r root before after) s) :
    Reachable r root s → Acc (fun after before => Actual r root before after) s := by
  induction limited with
  | intro state _ smaller =>
    intro seen
    refine .intro state ?_
    intro next move
    exact smaller next ((driver_exact seen).mpr move) (reachable_step seen move)

theorem raw_inaccessible {s : State roles} (startSeen : Reachable r root s)
    (no : ¬ Acc (fun after before => Actual r root before after) s) :
    ¬ Acc (fun after before => Driver r root before after) s :=
  fun bounded => no (acc_to_raw bounded startSeen)

theorem phase_reachable {chart : Chart F V} {codec : Codec roles Q}
    (reach : Reachable r root start) (path : B4Target.Steps (Step chart codec r root) start finish) :
    Reachable r root finish := by
  induction path with
  | refl => exact reach
  | tail _ move h => exact reachable_step h (GeneralRebasePhaseMachine281.raw move)

theorem guarded_path {chart : Chart F V} {codec : Codec roles Q}
    (reach : Reachable r root start) :
    B4Target.Steps (Guarded chart codec r root) start finish ↔
      B4Target.Steps (Step chart codec r root) start finish := by
  constructor
  · intro path
    induction path with
    | refl => exact .refl
    | tail _ move ih => exact .tail ih (guarded_raw move)
  · intro path
    induction path with
    | refl => exact .refl
    | @tail prior finish old last ih =>
      exact .tail ih ((guarded_exact (phase_reachable reach old)).mpr last)

theorem optional {source : State GeneralDictionaryJournalRefinement228Source.roles}
    (same : source = GeneralDictionaryVersionedInitialFrame233.before) :
    B4Target.Steps (Guarded GeneralRebaseChartFixtures281.outputChart GeneralRebasePhaseFixture281.codec
      GeneralDictionaryOptionalInitial229.sourceRegistry GeneralDictionaryJournalRefinement228Source.root)
      source GeneralDictionaryVersionedSecondInstall233.installed := by
  cases same
  apply (guarded_path ?_).mpr GeneralRebasePhaseFixture281.all_three
  exact ⟨_,⟨GeneralDictionaryOptionalInitial229.start,GeneralDictionaryOptionalInitial229.initial,rfl⟩,.refl⟩

namespace Version
open GeneralDictionaryVersionLoopSource237 (sourceRegistry initial)
local notation "loopRoot" => GeneralDictionaryVersionLoopSource237.root
local notation "loopRoles" => GeneralDictionaryVersionLoopSource237.roles
open GeneralRebasePhaseLoop281 (oldEmpty onceCodec)
open GeneralDictionaryVersionLoopIteration239 (state reachable)
open GeneralRebaseVersionMicro278 (installed)

theorem driver_not_acc : ¬ Acc (fun after before => Driver sourceRegistry loopRoot before after) initial :=
  raw_inaccessible (reachable 0) GeneralDictionaryVersionLoopNontermination239.initial_no_acc

theorem retains_first_round : B4Target.Steps (Guarded oldEmpty (onceCodec loopRoles) sourceRegistry loopRoot) initial (state 1) :=
  (guarded_path (reachable 0)).mpr GeneralRebasePhaseLoop281.Version.first_round

theorem excludes_repeat (n : Nat) : ¬ Guarded oldEmpty (onceCodec loopRoles) sourceRegistry loopRoot (state (n+1)) (installed (n+1)) :=
  fun step => GeneralRebasePhaseLoop281.Version.no_repeat n (guarded_raw step)

end Version

namespace Loose
open GeneralDictionaryLooseLoopSource240 (sourceRegistry initial)
local notation "loopRoot" => GeneralDictionaryLooseLoopSource240.root
local notation "loopRoles" => GeneralDictionaryLooseLoopSource240.roles
open GeneralRebasePhaseLoop281 (looseEmpty onceCodec)
open GeneralDictionaryLooseIterationIteration240 (state reachable)
open GeneralRebaseLooseMicro278 (installed)

theorem driver_not_acc : ¬ Acc (fun after before => Driver sourceRegistry loopRoot before after) initial :=
  raw_inaccessible (GeneralNominalPointTransport240.reachable_old (reachable 0))
    (fun h => GeneralDictionaryLooseIterationNontermination240.initial_no_acc (GeneralNominalPointErasure240.old_acc h))

theorem retains_first_round : B4Target.Steps (Guarded looseEmpty (onceCodec loopRoles) sourceRegistry loopRoot) initial (state 1) :=
  (guarded_path (GeneralNominalPointTransport240.reachable_old (reachable 0))).mpr GeneralRebasePhaseLoop281.Loose.first_round

theorem excludes_repeat (n : Nat) : ¬ Guarded looseEmpty (onceCodec loopRoles) sourceRegistry loopRoot (state (n+1)) (installed (n+1)) :=
  fun step => GeneralRebasePhaseLoop281.Loose.no_repeat n (guarded_raw step)

end Loose
end Yulang.GeneralRebaseCompiledRegressions282
