import Yulang.GeneralDeclarativeNestedSiblingsResult332
import Yulang.GeneralDeclarativeNestedModels332

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 22000000
namespace Yulang.GeneralDeclarativeNestedSiblingsModels332

open GeneralDeclarativeNestedSiblingsFrame332
open GeneralDeclarativeNestedSiblingsResult332 (dictionary every_model)
open GeneralDeclarativeNestedSiblingsDecl332 (registry)
open GeneralDeclarativeNestedDecl332 (root)
open GeneralDeclarativeNestedExample332 (interpretation outerRow innerRow scalar innerResidual outerResidual)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)

def model : Assignment := fun n =>
  if n = 10 then (GeneralDeclarativeNestedModels332.bool,Common.rowEmpty)
  else GeneralDeclarativeNestedModels332.model n

theorem original : Models source model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩,?_⟩
  intro row used
  change row ∈ [outerRow,innerRow,scalar,scalar11] at used
  simp only [List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with h|h|h|h <;> cases h <;> exact eqv_refl _

theorem named_model : Models namedStage model := by
  apply (model_append _).mpr
  refine ⟨original,fun row emitted => ?_⟩
  change row ∈ [⟨16,innerResidual⟩,⟨17,outerResidual⟩] at emitted
  rcases List.mem_cons.mp emitted with rfl|rest
  · exact eqv_refl _
  · cases List.mem_singleton.mp rest
    exact eqv_refl _

theorem stage_model : Models stage model :=
  ((actual_head (fun _ => False)).2.2.2.2 model).mpr named_model

theorem inhabited : ∃ m, Models final m := by
  obtain ⟨m0,h0,k0⟩ := (gathered (fun _ => False)).preserve.lifts model stage_model
  have parentFit : Models parent m0 := (model_append _).mpr ⟨h0,fun row used => by
    cases List.mem_singleton.mp used
    change Equivalent (m0 6).1 (m0 17).1
    rw [k0 6 (by decide +kernel),k0 17 (by decide +kernel)]
    exact eqv_refl _⟩
  obtain ⟨m1,h1,k1⟩ := gatheredOne.preserve.lifts m0 parentFit
  have oneFit : Models firstDone m1 := (model_append _).mpr ⟨h1,fun row used => by
    cases List.mem_singleton.mp used
    change Equivalent (m1 5).1 (m1 3).1
    rw [k1 5 (by decide +kernel),k1 3 (by decide +kernel),k0 5 (by decide +kernel),k0 3 (by decide +kernel)]
    exact eqv_refl _⟩
  obtain ⟨m2,h2,k2⟩ := gatheredTwo.preserve.lifts m1 oneFit
  refine ⟨m2,(model_append _).mpr ⟨h2,fun row used => ?_⟩⟩
  cases List.mem_singleton.mp used
  change Equivalent (m2 10).1 (m2 11).1
  rw [k2 10 (by decide +kernel),k2 11 (by decide +kernel),k1 10 (by decide +kernel),k1 11 (by decide +kernel),
    k0 10 (by decide +kernel),k0 11 (by decide +kernel)]
  exact eqv_refl _

theorem exact_siblings_same_model :
    first.arguments = [⟨18,3,19⟩] ∧ first.outputs = [⟨1,5⟩] ∧
    second.arguments = [⟨20,11,21⟩] ∧ second.outputs = [⟨1,10⟩] ∧
    ∃ m, Models final m ∧ Evidence registry interpretation m root dictionary := by
  obtain ⟨m,valid⟩ := inhabited
  exact ⟨rfl,rfl,rfl,rfl,m,valid,every_model m valid⟩

end Yulang.GeneralDeclarativeNestedSiblingsModels332
