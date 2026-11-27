import Yulang.GeneralDeclarativeWitnessNativePortTransport361
import Yulang.GeneralDeclarativeI65I74NativeProducerPhaseOrigin465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ExactForwardingReplay467
open GeneralDeclarativeWitnessNativeDirectSource361 (Direct sourceRoute Wire)
open GeneralDeclarativeWitnessNativePortTransport361 (Port transport)
open GeneralDeclarativeWitnessNativeRelease360 (checkExactRelease)
open GeneralDeclarativeI65.I72.NativeProducer465 (each_independent_active_address_replays)
open GeneralDeclarativeWitnessSequentialNative360 (Sequence)
open GeneralDeclarativeWitnessNestedInstall360 (Run)
open GeneralDeclarativeWitnessReleasedForward360 (forwardKey forwardDemand fixed)

theorem independent_direct_source_position_replays {env frame demand address w}
    (a : Direct env frame demand address w) :
    sourceRoute env frame demand address w = some a := by
  rcases a with ⟨impl,receiver,row,seed,operand,source,child,rowAt,argument,opAt,
    same,childSame,path,clauseId,head,only,inChild,point,checked,checkedChild⟩
  unfold sourceRoute
  split
  · rename_i actual actualChild found foundChild
    have first := Option.some.inj (source.symm.trans found)
    have second := Option.some.inj (child.symm.trans foundChild)
    subst actual
    subst actualChild
    split
    · rename_i liveClause liveArg atRow atArgument
      have sameRow := Option.some.inj (rowAt.symm.trans atRow)
      have sameArg := Option.some.inj (argument.symm.trans atArgument)
      subst liveClause
      subst liveArg
      split
      · rename_i missing
        rw [opAt] at missing
        cases missing
      · rename_i liveOp actualOp
        have sameOp := Option.some.inj (opAt.symm.trans actualOp)
        subst liveOp
        simp [same,childSame,path,clauseId,head,only,inChild,point,checked,checkedChild]
    · rename_i cannot
      exact (cannot _ _ rowAt argument).elim
  · rename_i cannot
    exact (cannot _ _ source child).elim

theorem independent_exact_forwarded_port_replays {negative} {r : Run negative}
    {seq : Sequence r} {gate w} (port : Port seq gate w) :
    transport seq gate w = some port := by
  rcases port with ⟨stated,released,actualAt,atInput,atSeed⟩
  have i : w.clausePosition = 0 := by
    rw [seq.exactReceiver] at actualAt
    cases index : w.clausePosition with
    | zero => rfl
    | succ i => simp [index] at actualAt
  have j : w.operandPosition = 0 := by
    rw [seq.args] at atInput
    cases index : w.operandPosition with
    | zero => rfl
    | succ i => simp [index] at atInput
  have rel : checkExactRelease seq.final.board gate r.typed.write = some released := by
    simp [checkExactRelease,each_independent_active_address_replays released.released,Option.bind,released.same]
  simp [transport,independent_direct_source_position_replays stated,rel,i,j,atSeed,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.ExactForwardingReplay467
