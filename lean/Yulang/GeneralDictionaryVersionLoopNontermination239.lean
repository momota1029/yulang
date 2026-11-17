import Yulang.GeneralDictionaryVersionLoopIteration239
set_option backward.isDefEq.respectTransparency false
/-! Closed obstruction to operational accessibility for the unchanged I44
mixed-source boundary. Every round is built from its actual guarded steps. -/
namespace Yulang.GeneralDictionaryVersionLoopNontermination239
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopStage239
open GeneralDictionaryVersionLoopIteration239
open GeneralNominalVersionedJournal232

abbrev reverseStep (after before : State roles) := GeneralNominalVersionedMixedKernel234.Step registry root before after

theorem backward_round (n : Nat) : Relation.TransGen reverseStep (state (n+1)) (state n) := by
 let stage := stages n
 have first := GeneralDictionaryVersionLoopInstall239.step stage.shape stage.valid stage.recorded (novel stage)
 have second := GeneralDictionaryVersionLoopFamilyRefresh238.step
   GeneralDictionaryVersionLoopBook239.allocations GeneralDictionaryVersionLoopBook239.reservations GeneralDictionaryVersionLoopBook239.atoms
   (GeneralDictionaryVersionLoopInstall239.installed stage.shape) n stage.shape.source rfl
   (GeneralDictionaryVersionLoopInstall239.installed_recorded stage.shape stage.recorded)
 have third := GeneralDictionaryVersionLoopFamilyReobserve238.step
   GeneralDictionaryVersionLoopBook239.allocations GeneralDictionaryVersionLoopBook239.reservations GeneralDictionaryVersionLoopBook239.atoms
   (GeneralDictionaryVersionLoopInstall239.installed stage.shape) n stage.shape.source
   (GeneralDictionaryVersionLoopInstall239.installed_recorded stage.shape stage.recorded)
 exact .tail (.tail (.single third) second) first

theorem no_acc (n : Nat) : ¬ Acc reverseStep (state n) := by
 intro accessible
 have closure := accessible.transGen
 clear accessible
 generalize equal : state n = current at closure
 induction closure generalizing n with
 | intro current _ ih =>
   have step : Relation.TransGen reverseStep (state (n+1)) current := equal ▸ backward_round n
   exact ih _ step (n+1) rfl

theorem initial_no_acc : ¬ Acc reverseStep initial := no_acc 0

theorem no_saturation (executor : B4TargetV3.Executor (GeneralNominalVersionedDiagnostic232.vocabulary roles)) :
 ¬ B4TargetV8.SaturationTotal (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) executor := by
 intro total
 exact initial_no_acc (total sourceRegistry ⟨rfl,source_checked⟩ initial root
   GeneralDictionaryVersionLoopInitial238.initial_source).1

theorem no_statement (executor : B4TargetV3.Executor (GeneralNominalVersionedDiagnostic232.vocabulary roles)) :
 ¬ B4TargetV8.Statement (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) executor := by
 intro statement
 exact no_saturation executor statement.1
end Yulang.GeneralDictionaryVersionLoopNontermination239
