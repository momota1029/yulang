import Yulang.GeneralDeclarativeWitnessTypedSource354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedScope354
open GeneralDeclarativeWitnessTypedForest354 (Input WriterWire Leaf Accepted)
open GeneralDeclarativeWitnessTypedPacket354 (Run)
open GeneralDeclarativeWitnessTypedRelease354 (address Key)
open GeneralDeclarativeWitnessTypedChild354 (physical_target)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)

theorem same_compiled_run {p s w i d} (a : Leaf p s w i d)
    (r : Run p.producer w.head)
    (runOK : GeneralDeclarativeWitnessTypedPacket354.run p.producer w.head = some r) :
    a.linked.writer.output = r :=
  Option.some.inj (a.linked.writer.ran.symm.trans runOK)

open GeneralDeclarativeWitnessCovariantOrigin353 (View assigned)
open GeneralDeclarativeWitnessTypedSound354 (childView released_type_at_actual_center)

theorem exact_scope {p s w i d} (a : Leaf p s w i d)
    (r : Run p.producer w.head)
    (runOK : GeneralDeclarativeWitnessTypedPacket354.run p.producer w.head = some r)
    (m : Assignment) (fit : Models s m) :
    r.children[i]? = some d ∧
    a.wire.path = p.location.path ++ [i] ∧
    p.producer.demand.outputs[a.plan.writtenOrdinal]? = some a.linked.emitted.atWrite.demand ∧
    w.out.trace[a.plan.writtenOrdinal]? = some (.typed a.linked.emitted.atWrite.typed.row) ∧
    a.linked.receiver.facts.arg.center = a.linked.emitted.atWrite.demand.target ∧
    address a.linked.writer p.location a.plan.writtenOrdinal a.linked.emitted.atWrite.demand ∈ p.authority.released ∧
    ∃ center : View,
      childView a.linked m a.linked.receiver.facts.arg.center = some center ∧
      center.tag = a.linked.emitted.atWrite.typed.tag ∧ center.box = a.linked.emitted.atWrite.typed.box ∧
      Common.Equivalent center.payload
        (.union (assigned m r.source.anchor.first.valueName).1
                (assigned m r.source.anchor.last.valueName).1) := by
  have cw := same_compiled_run a r runOK
  have child := a.linked.atChild
  change a.linked.writer.output.children[i]? = some a.linked.demand at child
  rw [cw,a.exactDemand] at child
  have written := GeneralDeclarativeWitnessTypedRelease354.exact_ordinal a.linked.emitted
  obtain ⟨seen,where_,tag,box,payload⟩ := released_type_at_actual_center a.linked m fit
  rw [cw] at payload
  exact ⟨child,a.exactPath,written.1,written.2.1,physical_target a.linked,a.linked.emitted.release,
    ⟨seen,where_,tag,box,payload⟩⟩

end Yulang.GeneralDeclarativeWitnessTypedScope354
