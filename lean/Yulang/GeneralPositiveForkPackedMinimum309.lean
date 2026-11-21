import Yulang.GeneralPositiveForkCertifiedTrace309
import Yulang.GeneralDictionaryGroundCopy218Refresh

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 14500000
namespace Yulang.GeneralPositiveForkPackedMinimum309
open GeneralPositiveForkPacked309 (Joint exact_joint footprint)
open GeneralPositiveForkEvidence309 (payload)
open GeneralPositiveForkInstall309 (inhabited)
open GeneralNominalExamples (model)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDisplayFrame285 (TypeCheck)
open GeneralRebaseQuestionFootprint298 (Footprint agrees)
open GeneralDictionaryReadback (Payload)
open CommonNominalFullCarrier
open GeneralNominalRecursiveInspection (Test)

def poison (name : Nat) : Assignment := fun i =>
  (if i = name then .top else (model i).1,(model i).2)

theorem genuine : Joint model payload (.node 2 []) (.node 3 []) :=
  (exact_joint _ _ _ _).mpr ⟨(GeneralPositiveForkPacked309.model_exact _).mp inhabited,rfl,rfl,rfl⟩

theorem poison_fails (i : Nat) (bounded : i ≤ 1) : ¬ TypeCheck (poison i) := by
  intro done
  have which : i = 0 ∨ i = 1 := by omega
  rcases which with rfl|rfl
  · have bad := done.2
    change Equivalent .top (nominal 0 [.inl (.base .int)]) at bad
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.nominal 0 1)
      ⟨[.inl (.base .int)],rfl,bad⟩
  · have bad := done.1
    change Equivalent .top (.base .int) at bad
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.scalar .int) bad

def FramesJoint (f : Footprint) : Prop :=
  ∀ a b, agrees f a b →
    (Joint a payload (.node 2 []) (.node 3 []) ↔ Joint b payload (.node 2 []) (.node 3 []))

theorem dependency (f : Footprint) (retains : FramesJoint f) (id : Nat) (needed : id ≤ 1) :
    id ∈ f.types := by
  apply Classical.byContradiction
  intro absent
  have agree : agrees f (poison id) model := by
    refine ⟨?_,fun _ _ => rfl⟩
    intro j included
    have different : j ≠ id := fun e => absent (e ▸ included)
    simp [poison,different]
  have live := (retains _ _ agree).mpr genuine
  exact poison_fails id needed ((exact_joint _ _ _ _).mp live).1

theorem minimum :
    FramesJoint footprint ∧ ∀ f, FramesJoint f → 0 ∈ f.types ∧ 1 ∈ f.types :=
  ⟨fun a b eq => GeneralPositiveForkPacked309.framing a b _ _ _ eq,
    fun f preserved => ⟨dependency f preserved 0 (by decide),dependency f preserved 1 (by decide)⟩⟩

end Yulang.GeneralPositiveForkPackedMinimum309
