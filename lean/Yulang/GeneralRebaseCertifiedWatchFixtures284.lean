import Yulang.GeneralRebaseWatchPathLift284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 11500000
namespace Yulang.GeneralRebaseCertifiedWatchFixtures284
open GeneralRebaseCertifiedWatchDriver284 (Node Step sound)
open GeneralRebaseWatchValidator284 (Compact Valid admits)
open GeneralRebaseWatchValidatorSource284 (candidate)
open GeneralRebaseWatchPathLift284 (Coverage)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseMixedCounts277 (Actual)

namespace Display
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralRebaseDisplayFrame276 (before)
open GeneralRebaseCompiledDisplay277 (after effect)
open GeneralRebaseDisplayWatch284 (watch stored next_valid checker input_valid history_empty packet_empty)
open GeneralRebaseCachedFixtures283.Display (source_start)

noncomputable def begin : Node roles := ⟨before,stored⟩
noncomputable def done : Node roles := ⟨after,stored⟩

theorem one_step : Step registry displayRoot begin done :=
  GeneralRebaseCertifiedWatchDriver284.install_lift source_start input_valid .root
    GeneralRebaseCompiledInstall277.installable GeneralRebaseCompiledInstall277.novel rfl checker
    (fun {_} req => List.mem_append_left _ (List.mem_append_right _ req))

theorem terminal (next : Node roles) : ¬ Step registry displayRoot done next :=
  fun moves => GeneralRebaseCompiledStable277.halted next.raw (sound moves)

theorem every_raw_endpoint (s : GeneralNominalVersionedJournal232.State roles)
    (walk : B4Target.Steps (Actual registry displayRoot) before s) :
    s = before ∨ s = after := by
  induction walk with
  | refl => exact Or.inl rfl
  | @tail previous s older edge ih =>
    rcases ih with rfl|rfl
    · exact Or.inr ((GeneralRebaseCompiledAcc277.adapter_next _).mp edge)
    · exact False.elim (GeneralRebaseCompiledStable277.halted _ edge)

theorem all_routes (s : GeneralNominalVersionedJournal232.State roles) :
    B4Target.Steps (Actual registry displayRoot) before s ↔
    ∃ q : Node roles, q.raw = s ∧ B4Target.Steps (Step registry displayRoot) begin q := by
  constructor
  · intro route
    rcases every_raw_endpoint s route with rfl|rfl
    · exact ⟨begin,rfl,.refl⟩
    · exact ⟨done,rfl,.tail .refl one_step⟩
  · rintro ⟨q,rfl,path⟩
    exact GeneralRebaseCertifiedWatchDriver284.accepted_routes path

def emptyWatch : Compact := ⟨0,[],[]⟩

theorem validator_not_source_rejection :
    Valid emptyWatch (history before) ∧ candidate emptyWatch [0] effect = none ∧
      Actual registry displayRoot before after := by
  constructor
  · rw [history_empty]
    exact ⟨fun _ h => False.elim (List.not_mem_nil h),
      ⟨fun _ h => False.elim (List.not_mem_nil h),fun {_} h => h,fun _ h => False.elim (List.not_mem_nil h)⟩,
      List.Pairwise.nil⟩
  · have blocked : admits 0 [] [0] = false := rfl
    refine ⟨?_,GeneralRebaseCompiledInstall277.adapter_step⟩
    unfold candidate
    rw [packet_empty]
    exact (GeneralRebaseWatchValidator284.local_only emptyWatch [0] []).mpr (Or.inl blocked)

end Display

namespace Optional
open GeneralDictionaryOptionalInitial229 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (effect installed)
open GeneralRebaseOptionalWatch284 (watch saved)
open GeneralRebaseOptionalOverwrite282 (point_reached)

theorem accepted :
    ∃ current : Node roles, current.raw = installed ∧
      Step sourceRegistry root ⟨point,saved⟩ current := by
  obtain ⟨next,inv,_⟩ := GeneralRebaseOptionalWatch284.certified_install
  have align := GeneralRebaseWatchValidatorSource284.watch_unchanged inv
  have model := GeneralNominalVersionedMixedKernel234.of_old_installable
    GeneralDictionaryVersionedSecondStep233.installable
  exact ⟨⟨installed,next⟩,rfl,GeneralRebaseCertifiedWatchDriver284.install_lift
    point_reached GeneralRebaseOptionalWatch284.prior_good .root model
    GeneralDictionaryVersionedSecondStep233.not_committed rfl (align.symm ▸ inv)
    (align.symm ▸ (fun {_} h => List.mem_append_right _ h))⟩

end Optional

end Yulang.GeneralRebaseCertifiedWatchFixtures284
