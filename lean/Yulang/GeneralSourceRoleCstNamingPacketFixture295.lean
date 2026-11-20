import Yulang.GeneralSourceRoleCstNamingPacket295

/-! Synthetic finite packet data follows the actually used old name lookups.
The trace is not an authority to invent a valid language environment. -/
set_option maxRecDepth 16000
set_option maxHeartbeats 2200000
namespace Yulang.GeneralSourceRoleCstNamingPacketFixture295
open GeneralSourceRoleCstNamingTrace295 (Trace)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary captureAt checked)
open GeneralSourceRoleCstSelectedControl295 (first second packet both naming actualRead)
open GeneralSourceRoleCstNamingControl295 (shiftedCtor irrelevant)
open GeneralSourceRoleResolverFixture292 (parameterTable charTable)
open Roles.Examples (int)
open Roles.AssocExamples (char)

def binderTrace : Trace := [(.role "Index",some 2),(.output 2 "value",some 0)]
def ctorTrace : Trace := binderTrace ++ [(.constructor "char",some 3)]
def pinnedFirst : FiniteBoundary Nat Nat := ⟨packet first,binderTrace⟩
def pinnedSecond : FiniteBoundary Nat Nat := ⟨packet second,ctorTrace⟩

theorem exactly_consumed :
    captureAt .selectedBranch 5 both 71 first (packet first) naming = some binderTrace ∧
    captureAt .selectedBranch 5 both 71 second (packet second) naming = some ctorTrace :=
  ⟨rfl,rfl⟩

theorem altered_shape_denied :
    checked .selectedBranch 5 both 71 first ⟨packet first,[]⟩ naming 2 = none ∧
    checked .selectedBranch 5 both 71 first ⟨packet first,binderTrace.reverse⟩ naming 2 = none ∧
    checked .selectedBranch 5 both 71 first ⟨packet first,ctorTrace⟩ naming 2 = none :=
  ⟨rfl,rfl,rfl⟩

theorem consumed_constructor_value_checked :
    checked .selectedBranch 5 both 71 second pinnedSecond naming 2 = some charTable ∧
    checked .selectedBranch 5 both 71 second pinnedSecond shiftedCtor 2 = none ∧
    checked .selectedBranch 5 both 71 first pinnedFirst shiftedCtor 2 = some parameterTable :=
  ⟨rfl,rfl,rfl⟩

theorem exact_packet_respects_locality :
    checked .selectedBranch 5 both 71 first pinnedFirst irrelevant 2 = some parameterTable := rfl

end Yulang.GeneralSourceRoleCstNamingPacketFixture295
