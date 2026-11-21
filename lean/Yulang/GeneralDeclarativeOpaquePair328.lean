import Yulang.GeneralDeclarativeOpaqueChannel328
import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000
namespace Yulang.GeneralDeclarativeOpaquePair328
open CommonNominalFullCarrier (Ty Row pair observeTy Subtype Equivalent subtype_trans common_pair_iff)
open GeneralDeclarativeOpaqueChannel328 (project channel tests probe_step)
open CommonNominalFullDemand (Observation Environment ProbeAt ProbeStep MaskedProbeStep)
open CommonNominalSyntax (Layer graph observe)

def pairChannel : Observation Row → Prop
  | .pairFirst _ | .pairLast _ => True
  | _ => False

theorem off_channel (depth rank : Nat) (env : Environment Row) (o : Observation Row)
    (notPair : ¬pairChannel o) (a b c d : Ty) :
    ProbeAt Common.rowLe rank env (observeTy depth (pair a b)) o ↔
      ProbeAt Common.rowLe rank env (observeTy depth (pair c d)) o := by
  cases o <;> cases rank <;>
    simp_all [pairChannel,ProbeAt,ProbeStep,MaskedProbeStep,pair,observeTy,Layer.evalAt]

theorem at_channel (last : Bool) (depth rank : Nat) (env : Environment Row) (o : Observation Row)
    (input payload : Ty) (given : project last input = some payload) :
    ProbeAt Common.rowLe rank env (observeTy (depth+1) input) (channel last o) ↔
      ProbeAt Common.rowLe rank env (observeTy depth payload) o := by
  cases rank
  · simpa only [ProbeAt,ProbeStep,given,tests] using
      probe_step last depth env (fun _ _ => True) o input []
  · rename_i rank
    simpa only [ProbeAt,ProbeStep,given,tests] using
      probe_step last depth env (fun expected input =>
        ∀ next obs, ProbeAt Common.rowLe rank next input obs → ProbeAt Common.rowLe rank next expected obs) o input []

theorem pair_observed (last : Bool) (depth rank : Nat) (env : Environment Row) (o : Observation Row)
    (a b : Ty) :
    ProbeAt Common.rowLe rank env (observeTy (depth+1) (pair a b)) (channel last o) ↔
      ProbeAt Common.rowLe rank env (observeTy depth (if last then b else a)) o := by
  apply at_channel
  cases last <;> rfl

theorem pair_zero (last : Bool) (rank : Nat) (env : Environment Row) (o : Observation Row) (a b : Ty) :
    ProbeAt Common.rowLe rank env (observeTy 0 (pair a b)) (channel last o) := by
  cases last <;> cases rank <;> cases o <;>
    simp [channel,ProbeAt,ProbeStep,MaskedProbeStep,pair,observeTy,Layer.evalAt,observe]

theorem present (last : Bool) (x u v : Ty) (upper : Subtype x (pair u v)) :
    ∃ payload, project last x = some payload := by
  let env : Environment Row := ⟨fun _ => .bottom,fun _ => []⟩
  have head : ProbeAt Common.rowLe 0 env (observeTy 1 (pair u v)) (channel last .trivial) :=
    (pair_observed last 0 0 env .trivial u v).mpr (by
      cases q : observeTy 0 (if last then v else u) <;> trivial)
  have reached := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (upper 1) 0 env
    (channel last .trivial) head
  have channelTest := (probe_step last 0 env (fun _ _ => True) .trivial x []).mp reached
  cases chosen : project last x with
  | none => simp [chosen,tests] at channelTest
  | some a => exact ⟨a,rfl⟩

/-- Upper-bounded paired values have each observation channel; the
lower pair supplies the non-channel side of reconstruction. The model
center can be arbitrary regular syntax, not an ordinary pair row or
a chosen semantic point from the endpoints. -/
theorem reconstruction (x loA loB hiA hiB : Ty)
    (low : Subtype (pair loA loB) x) (high : Subtype x (pair hiA hiB)) :
    ∃ a b, project false x = some a ∧ project true x = some b ∧ Equivalent x (pair a b) := by
  obtain ⟨a,left⟩ := present false x hiA hiB high
  obtain ⟨b,right⟩ := present true x hiA hiB high
  have same (depth : Nat) : CommonNominalFullDemand.ProducerEq Common.rowLe
      (observeTy depth x) (observeTy depth (pair a b)) := by
    apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
    intro rank env o
    have lowProbe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (low depth) rank env o
    have highProbe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (high depth) rank env o
    have outside (notPair : ¬pairChannel o) :
        ProbeAt Common.rowLe rank env (observeTy depth x) o ↔
          ProbeAt Common.rowLe rank env (observeTy depth (pair a b)) o :=
      ⟨fun original => (off_channel depth rank env o notPair loA loB a b).mp (lowProbe original),
       fun rebuilt => highProbe ((off_channel depth rank env o notPair a b hiA hiB).mp rebuilt)⟩
    have inside (last : Bool) (q : Observation Row) (eq : o = channel last q) :
        ProbeAt Common.rowLe rank env (observeTy depth x) o ↔
          ProbeAt Common.rowLe rank env (observeTy depth (pair a b)) o := by
      subst o
      cases depth with
      | zero =>
        exact ⟨fun _ => pair_zero last rank env q a b,
          fun _ => highProbe (pair_zero last rank env q hiA hiB)⟩
      | succ depth =>
        cases last
        · exact (at_channel false depth rank env q x a left).trans (pair_observed false depth rank env q a b).symm
        · exact (at_channel true depth rank env q x b right).trans (pair_observed true depth rank env q a b).symm
    cases o
    case pairFirst p => exact inside false p rfl
    case pairLast p => exact inside true p rfl
    all_goals exact outside (by simp [pairChannel])
  exact ⟨a,b,left,right,⟨fun d => (same d).1,fun d => (same d).2⟩⟩

theorem projected_intervals (x loA loB hiA hiB : Ty)
    (low : Subtype (pair loA loB) x) (high : Subtype x (pair hiA hiB)) :
    ∃ a b, project false x = some a ∧ project true x = some b ∧ Equivalent x (pair a b) ∧
      (Subtype loA a ∧ Subtype a hiA) ∧ (Subtype loB b ∧ Subtype b hiB) := by
  obtain ⟨a,b,readA,readB,paired⟩ := reconstruction x loA loB hiA hiB low high
  have lo := (common_pair_iff ..).mp (subtype_trans low paired.1)
  have hi := (common_pair_iff ..).mp (subtype_trans paired.2 high)
  exact ⟨a,b,readA,readB,paired,⟨lo.1,hi.1⟩,⟨lo.2,hi.2⟩⟩

end Yulang.GeneralDeclarativeOpaquePair328
