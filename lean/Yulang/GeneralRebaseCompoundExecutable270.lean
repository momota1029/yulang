import Yulang.GeneralRebaseSingleExitCode270
import Yulang.GeneralRebaseCompoundProjection270

namespace Yulang.GeneralRebaseCompoundExecutable270
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralRebaseSourceStrictFixture265 (owners pool)
open GeneralRebaseCompoundProjection270 (initial_full initial_rank all_weak_targets some_weak_target)
open GeneralRebaseBehavior269 (code)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseSingleExitCode270 (compile)
open FiniteRankBehavior269 (Code)
open FiniteBehaviorDriver269 (drive Advances)
open GeneralRebaseStep258 (Fact)

def actualBasis : List Fact :=
 Basis [GeneralNominalIdentities.pair root.identity declaration.id] [⟨0,4⟩]

theorem actualBasis_exact : actualBasis = Basis owners pool := rfl

def initialCode : Code (List Fact) := compile actualBasis actualBasis

theorem initialCode_exact : code registry root owners pool before = initialCode := by
 unfold initialCode
 rw [actualBasis_exact]
 have full := GeneralRebaseSingleExitCode270.exact_code registry root owners pool before ⟨installed,some_weak_target⟩ all_weak_targets
 simpa only [initial_full] using full

theorem computed_shape : initialCode = .node actualBasis [.node [] []] := by rfl

def run : Nat × Code (List Fact) := drive 2 initialCode

theorem computed_run : run = (1,.node [] []) := by rw [run,computed_shape]; rfl

theorem computed_exit : Advances initialCode (.node [] []) := by
 rw [computed_shape]
 exact List.mem_singleton_self _

/-- The real initial state has exactly one *behavioral* weak child code,
including all original weak paths, not exactly one concrete successor. -/
theorem verified_all_exits {target : Code (List Fact)} : Advances initialCode target ↔ target = .node [] [] := by
 rw [computed_shape]
 exact List.mem_singleton

theorem verified_terminal : ∃ after,
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) before after ∧
 run.2.label = (project owners pool after).remaining ∧
 (∀ future, B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) after future →
   project owners pool future = project owners pool after) := by
 have exactBudget : (Basis owners pool).length = 2 :=
   (congrArg List.length initial_full).symm.trans initial_rank
 obtain ⟨after,oldPath,label,stable,_⟩ :=
   GeneralRebaseBehavior269.settle registry root owners pool before
 refine ⟨after,oldPath,?_,stable⟩
 simpa only [exactBudget,initialCode_exact,run] using label

end Yulang.GeneralRebaseCompoundExecutable270
