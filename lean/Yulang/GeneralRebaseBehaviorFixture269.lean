import Yulang.GeneralRebaseRankOne269
import Yulang.GeneralRebaseCompilerFixture268
import Yulang.GeneralRebaseSourceStrictFixture265

set_option maxRecDepth 18000
set_option maxHeartbeats 5000000
namespace Yulang.GeneralRebaseBehaviorFixture269
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryCompoundSource238 (sourceRegistry)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralRebaseSourceStrictFixture265 (owners pool strict)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseBehavior269 (code advance_exact)
open GeneralRebaseWeakProgress268 (Weak)
open FiniteRankBehavior269 (Code)
open FiniteBehaviorDriver269 (Advances)
open GeneralRebaseStep258 (Fact)

def exitCode : Code (List Fact) := .node [] []

theorem exhausted : (project owners pool installed).remaining = [] := by decide +kernel

theorem checked_exit :
 GeneralRebaseRankOne269.tryCode (Basis owners pool) (project owners pool installed).remaining none =
 some exitCode := by rw [exhausted]; rfl

theorem exact_exit : code sourceRegistry root owners pool installed = exitCode :=
 GeneralRebaseRankOne269.sound sourceRegistry root owners pool installed none True.intro checked_exit

theorem actual_advance : Weak sourceRegistry root owners pool before installed :=
 ⟨before,.refl,GeneralRebaseCompilerFixture268.actual_generated_install.1,strict⟩

theorem listed_exit : Advances (code sourceRegistry root owners pool before) exitCode :=
 (advance_exact sourceRegistry root owners pool before exitCode).mpr ⟨installed,actual_advance,exact_exit⟩

/-- The actual source-derived 238 install has a verified empty continuation
code. A complete executable catalogue for every other possible transition
from the initial rank-two source is not claimed. -/
theorem actual_exit_stable : ∀ after,
 B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step sourceRegistry root) installed after →
 project owners pool after = project owners pool installed := by
 apply (GeneralRebaseBehavior269.terminal_iff sourceRegistry root owners pool installed).mp
 rw [exact_exit]
 rfl

end Yulang.GeneralRebaseBehaviorFixture269
