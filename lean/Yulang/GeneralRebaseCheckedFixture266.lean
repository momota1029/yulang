import Yulang.GeneralRebaseSourceStrictFixture265
import Yulang.GeneralRebaseCheckedWrite259
import Yulang.GeneralRebaseBudget258

set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Yulang.GeneralRebaseCheckedFixture266
open GeneralRebaseSourceStrictFixture265
open GeneralRebaseStep258
open GeneralRebaseCheckedWrite259 (commit)

/-- All concrete proposed facts fit the hand-checked singleton output pool;
this is stronger than just exhibiting one fact that effects a strict change. -/
theorem closed : proposed ⊆ GeneralRebaseUniversalBasis263.basis owners pool := by
 have noUnsupported : GeneralRebaseCheckedWrite259.outside
     (GeneralRebaseUniversalBasis263.basis owners pool) proposed = [] := by decide +kernel
 exact (GeneralRebaseCheckedWrite259.closed_iff proposed).mp noUnsupported

theorem first_checked : commit first proposed = .ok (some last) := by
 apply (GeneralRebaseCheckedWrite259.accepted ..).mpr
 refine ⟨closed,(tryWrite_exact ..).mpr ⟨square,?_⟩⟩
 exact fun same => strict (state_ext _ _ same)

/-- The same concrete proposal has no further effect. It does not imply that
another, previously unseen, proposal cannot advance this abstract state. -/
theorem repeat_checked : commit last proposed = .ok none := by
 apply (GeneralRebaseCheckedWrite259.accepted ..).mpr
 exact ⟨closed,by rw [square]; exact GeneralRebaseBudget258.duplicate_noop _ _⟩

end Yulang.GeneralRebaseCheckedFixture266
