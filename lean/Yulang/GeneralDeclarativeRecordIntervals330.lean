import Yulang.GeneralDeclarativeRecordProbe330
import Yulang.CommonNominalFullModel

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRecordIntervals330
open CommonNominalFullCarrier (Ty Row Subtype observeTy record)
open CommonNominalFullDemand (Environment Observation ProbeAt ProbeStep MaskedProbeStep)
open GeneralDeclarativeRecordChannel330 (project channel test_some)
open GeneralDeclarativeRecordProbe330 (probe read)

theorem direct (key : Nat) (optional : Bool) (f rest : Ty) :
    project key optional [] (record key f rest) = some f := by
  simp [record,project,GeneralDeclarativeRecordChannel330.shows]

theorem projected_below (key : Nat) (optional : Bool) {x y a b : Ty}
    (left : project key optional [] x = some a) (right : project key optional [] y = some b)
    (below : Subtype x y) : Subtype a b := by
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env observation seen
  have step := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below (depth+1)) rank env
    (channel optional key observation)
  exact (read key depth rank env x a observation optional left).mp
    (step ((read key depth rank env y b observation optional right).mpr seen))

theorem present (key : Nat) (optional : Bool) {x b rest : Ty}
    (below : Subtype x (record key b rest)) : ∃ v, project key optional [] x = some v := by
  let env : Environment Row := ⟨fun _ => .bottom,fun _ => []⟩
  have checked : ProbeAt Common.rowLe 0 env (observeTy 1 (record key b rest)) (channel optional key .trivial) :=
    (read key 0 0 env _ _ .trivial optional (direct key optional b rest)).mpr (by
      cases inside : observeTy 0 b <;> simp [ProbeAt,ProbeStep,MaskedProbeStep])
  have found := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 1) 0 env _ checked
  have out := (probe key 0 env (fun _ _ => True) x optional [] .trivial).mp found
  cases field : project key optional [] x with
  | none => simp [field,GeneralDeclarativeOpaqueChannel328.tests] at out
  | some val => exact ⟨val,rfl⟩

/-- Both record modes independently inherit the source field bounds.
No equation asserting that a full record can be rebuilt from just
the required payload alone follows from this theorem. -/
theorem sandwich (key : Nat) (optional : Bool) {x a b tail1 tail2 : Ty}
    (lower : Subtype (record key a tail1) x) (upper : Subtype x (record key b tail2)) :
    ∃ v, project key optional [] x = some v ∧ Subtype a v ∧ Subtype v b := by
  obtain ⟨v,observed⟩ := present key optional upper
  exact ⟨v,observed,projected_below key optional (direct key optional a tail1) observed lower,
    projected_below key optional observed (direct key optional b tail2) upper⟩

end Yulang.GeneralDeclarativeRecordIntervals330
