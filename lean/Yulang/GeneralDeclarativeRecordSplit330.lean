import Yulang.GeneralDeclarativeRecordIntervals330
import Yulang.CommonNominalFullConstructors
import Yulang.GeneralNominalTopObservation

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
namespace Yulang.GeneralDeclarativeRecordSplit330
open CommonNominalFullCarrier (Ty Row Subtype Equivalent observeTy record exactEmpty common_inter_is_meet subtype_refl common_record_mono)
open CommonNominalFullDemand (Environment ProbeAt ProbeStep MaskedProbeStep)
open CommonNominalSyntax (Layer graph observe)
open GeneralDeclarativeRecordChannel330 (project channel)
open GeneralDeclarativeRecordProbe330 (read)
open GeneralDeclarativeRecordIntervals330 (direct)

def lo (key : Nat) : Ty := record key .bottom exactEmpty
def hi (key : Nat) : Ty := record key .top exactEmpty
def hidden (key : Nat) : Ty := .inter (hi key) exactEmpty

theorem bottom (v : Ty) : Subtype .bottom v := by
  intro d
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro r env obs _
  cases r <;> cases obs <;> trivial

theorem lower_agrees (key : Nat) : Subtype (lo key) exactEmpty := by
  intro d
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro r env obs found
  cases d <;> cases r <;> cases obs <;>
    simp_all [lo,record,exactEmpty,ProbeAt,ProbeStep,MaskedProbeStep,observeTy,Layer.evalAt,observe]
  all_goals (rename_i child; intro _; cases child <;> trivial)

theorem interval (key : Nat) : Subtype (lo key) (hidden key) ∧ Subtype (hidden key) (hi key) := by
  refine ⟨(common_inter_is_meet ..).mpr ⟨common_record_mono key (bottom _) (subtype_refl _),
    lower_agrees key⟩,((common_inter_is_meet ..).mp (subtype_refl _)).1⟩

theorem required_top (key : Nat) : project key false [] (hidden key) = some .top := by
  simp [hidden,hi,project,direct,exactEmpty,GeneralDeclarativeOpaqueChannel328.meet]
theorem optional_bottom (key : Nat) :
    project key true [] (hidden key) = some (.inter .top .bottom) := by
  simp [hidden,hi,project,direct,exactEmpty,GeneralDeclarativeOpaqueChannel328.meet]

def env : Environment Row := ⟨fun _ => .bottom,fun _ => []⟩

theorem required_rejects (key : Nat) :
    ¬ProbeAt Common.rowLe 0 env (observeTy 1 (hidden key)) (.field key (.base .int)) := by
  intro test
  have gone := (read key 0 0 env _ _ (.base .int) false (required_top key)).mp test
  exact gone

theorem optional_accepts (key : Nat) :
    ProbeAt Common.rowLe 0 env (observeTy 1 (hidden key)) (.optional key (.base .int)) :=
  (read key 0 0 env _ _ (.base .int) true (optional_bottom key)).mpr (.inr trivial)

/-- Neither endpoint is being selected as a model center. Even between
two required records of the same outer label, the observed required
and optional channels can differ. Any direct record at that label
has one payload for both, so a same-label peel is not sound in general. -/
theorem no_literal (key : Nat) (f rest : Ty) :
    ¬Equivalent (hidden key) (record key f rest) := by
  intro same
  have optional := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (same.2 1) 0 env
    (.optional key (.base .int)) (optional_accepts key)
  have observed := (read key 0 0 env _ _ (.base .int) true (direct key true f rest)).mp optional
  have field := (read key 0 0 env _ _ (.base .int) false (direct key false f rest)).mpr observed
  exact required_rejects key ((CommonNominalFullDemand.producerLe_iff_probe _ _).mp (same.1 1) 0 env
    (.field key (.base .int)) field)

theorem obstruction (key : Nat) :
    Subtype (lo key) (hidden key) ∧ Subtype (hidden key) (hi key) ∧
      ∀ payload tail, ¬Equivalent (hidden key) (record key payload tail) :=
  ⟨(interval key).1,(interval key).2,no_literal key⟩

end Yulang.GeneralDeclarativeRecordSplit330
