import Yulang.GeneralDeclarativeRecordChannel330

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDeclarativeRecordProbe330
open CommonNominalFullCarrier (Ty Row observeTy Subtype)
open CommonNominalSyntax (Layer graph observe)
open CommonNominalFullDemand (Observation Environment MaskedProbeStep ProbeAt ProbeStep)
open GeneralDeclarativeRecordChannel330 (channel project shows addTrivial defaultField test_some top_only optional_extra default_extra)
open GeneralDeclarativeOpaqueChannel328 (tests tests_union tests_meet)

theorem probe (key depth : Nat) (env : Environment Row) (order) (value : Ty)
    (optional : Bool) (hidden : List Nat) (obs : Observation Row) :
    MaskedProbeStep Common.rowLe env order hidden (observeTy (depth+1) value) (channel optional key obs) ↔
      tests depth env order obs (project key optional hidden value) := by
  induction value generalizing optional hidden obs with
  | union a b ih jh =>
    rw [project,tests_union]
    cases optional
    · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep] using and_congr (ih false hidden obs) (jh false hidden obs)
    · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep] using and_congr (ih true hidden obs) (jh true hidden obs)
  | inter a b ih jh =>
    rw [project,tests_meet]
    cases optional
    · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep] using or_congr (ih false hidden obs) (jh false hidden obs)
    · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep] using or_congr (ih true hidden obs) (jh true hidden obs)
  | mask hiddenMore source ih =>
    cases optional
    · simpa [channel,project,observeTy,Layer.evalAt,MaskedProbeStep] using ih false (hidden ++ hiddenMore) obs
    · simpa [channel,project,observeTy,Layer.evalAt,MaskedProbeStep] using ih true (hidden ++ hiddenMore) obs
  | bottom => cases optional <;> cases obs <;> simp [channel,project,tests,observeTy,Layer.evalAt,MaskedProbeStep]
  | emptyRecord =>
    cases optional
    · rfl
    · exact (top_only depth env order obs).symm
  | exactEmpty =>
    cases optional
    · rfl
    · by_cases h : key ∈ hidden <;> cases obs <;>
        simp [channel,project,h,tests,observeTy,Layer.evalAt,MaskedProbeStep]
  | record label payload tail ih =>
    by_cases selected : shows key label hidden
    · have hit : key = label ∧ label ∉ hidden := selected
      rw [project,ite_eq_left selected]
      cases optional <;>
        simp [channel,hit,tests,observeTy,Layer.evalAt,MaskedProbeStep,observe]
    · have miss : ¬(key = label ∧ label ∉ hidden) := selected
      rw [project,ite_eq_right selected,optional_extra]
      cases optional
      · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep,miss] using ih false hidden obs
      · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep,miss] using
          (or_congr (ih true hidden obs) (Iff.rfl : (obs = .trivial) ↔ obs = .trivial))
  | recordDefault label source payload ih =>
    rw [project,optional_extra]
    by_cases selected : shows key label hidden
    · have hit : key = label ∧ label ∉ hidden := selected
      rw [ite_eq_left selected,default_extra]
      have a := and_congr (ih true hidden obs) (or_congr (ih false hidden .trivial)
        (Iff.rfl : tests depth env order obs (some (graph Row payload)) ↔ _))
      cases optional
      · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep,hit,tests,observe] using a
      · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep,hit,tests,observe] using
          (or_congr a (Iff.rfl : (obs = .trivial) ↔ obs = .trivial))
    · have miss : ¬(key = label ∧ label ∉ hidden) := selected
      rw [ite_eq_right selected]
      cases optional
      · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep,miss] using ih false hidden obs
      · simpa [channel,observeTy,Layer.evalAt,MaskedProbeStep,miss] using
          (or_congr (ih true hidden obs) (Iff.rfl : (obs = .trivial) ↔ obs = .trivial))
  | base | float | top | pair | variant | arrow | nominal =>
    cases optional <;> rfl

theorem read (key depth rank : Nat) (env : Environment Row) (v payload : Ty) (obs : Observation Row)
    (optional : Bool) (p : project key optional [] v = some payload) :
    ProbeAt Common.rowLe rank env (observeTy (depth+1) v) (channel optional key obs) ↔
      ProbeAt Common.rowLe rank env (observeTy depth payload) obs := by
  cases rank
  · simpa only [ProbeAt,ProbeStep,p,tests] using probe key depth env (fun _ _ => True) v optional [] obs
  · rename_i rank
    simpa only [ProbeAt,ProbeStep,p,tests] using
      probe key depth env (fun expected input => ∀ next obs, ProbeAt Common.rowLe rank next input obs →
        ProbeAt Common.rowLe rank next expected obs) v optional [] obs

end Yulang.GeneralDeclarativeRecordProbe330
