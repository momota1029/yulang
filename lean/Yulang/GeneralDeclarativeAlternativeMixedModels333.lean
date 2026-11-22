import Yulang.GeneralDeclarativeAlternativeMixedCase333

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDeclarativeAlternativeMixedModels333
open GeneralDeclarativeAlternativeMixedCase333
open GeneralDeclarativeAlternativeMixedDecl333
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeAlternativeMixedReplay333 (frame_from_replay)
open GeneralDeclarativeAlternativeNeeds333 (finiteIndex)
open GeneralDeclarativeStableAssemble329 (MergeFacts)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOpaqueNominal328 (point_bounded)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeExampleSource320 (int)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty exactEmpty record variant)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

abbrev pairType := CommonNominalFullCarrier.pair int int
abbrev recordType := record 7 int exactEmpty
abbrev variantType := variant 4 pairType
def model : Assignment := fun n =>
  (if n = 0 ∨ n = 2 ∨ n = 9 then recordType else
    if n = 8 ∨ n = 6 ∨ n = 10 then variantType else
      if n = 5 then exactEmpty else if n = 7 then pairType else int,Common.rowEmpty)

theorem original : Models state model := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,?_⟩,?_⟩
  · intro pair located
    change pair ∈ [(2,0),(0,9),(6,8),(8,10)] at located
    simp only [List.mem_cons,List.not_mem_nil,or_false] at located
    rcases located with a|b|c|d <;> cases ‹_› <;> exact CommonNominalFullCarrier.subtype_refl _
  · intro row placed
    change row ∈ rows at placed
    simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at placed
    rcases placed with a|b|c|d|e|f|g|h
      <;> cases ‹_› <;> exact eqv_refl _

theorem remembered : Models observed model := by
  apply (model_append _).mpr
  refine ⟨original,fun row emitted => ?_⟩
  cases List.mem_singleton.mp emitted
  exact eqv_refl _

theorem folded : MergeFacts observed keep spans fallback := by
  apply GeneralDeclarativeStableAssemble329.assemble
  intro slot present
  change slot ∈ [(0,GeneralDeclarativeOpaqueNominal328.point 3),(1,GeneralDeclarativeOpaqueNominal328.point 5),
    (3,GeneralDeclarativeOpaqueNominal328.point 11),(4,GeneralDeclarativeOpaqueNominal328.point 12)] at present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with a|b|c|d <;> cases ‹_› <;> exact point_bounded _ _

theorem inhabited : ∃ m, Models compiled m := by
  obtain ⟨m,now,_⟩ := folded.preserve.lifts model remembered
  exact ⟨m,now⟩

theorem declared_frame (done : Nat → Prop) :
    ∃ frame : Frame compiled registry interpretation root decl [child], frame.targets = targets := by
  obtain ⟨packet,depth,proved⟩ := mixed_exact_receipt done
  have fits : ∀ a ∈ root.arguments, Bounds state a := by
    intro a found
    rcases List.mem_cons.mp found with rfl|remaining
    · exact bounds_one
    · cases List.mem_singleton.mp remaining
      exact bounds_two
  exact frame_from_replay view (finiteIndex packet) checked covered List.mem_cons_self rfl declared
    fits (proved depth (Nat.le_refl _))

/-- Both real source modes occur in the *same* checked two-argument
declaration. Real endpoint evidence enables compilation; it does not
replace either current center. The emitted child and its logical
target belong to the same ordinary inhabited state. No Local
diagnostic or stopped-Sat claim is added. -/
theorem actual_mixed_child :
    child.arguments = [⟨15,3,16⟩] ∧ child.outputs = [⟨1,14⟩] ∧
    ∃ frame : Frame compiled registry interpretation root decl [child],
      frame.targets = targets ∧
      ∃ m, Models compiled m ∧ Meaning registry interpretation m root decl frame.capture [child] := by
  obtain ⟨frame,whereTargets⟩ := declared_frame (fun _ => False)
  obtain ⟨m,fit⟩ := inhabited
  exact ⟨rfl,rfl,frame,whereTargets,m,fit,
    (read checked covered List.mem_cons_self rfl declared frame).2.1 m fit⟩

end Yulang.GeneralDeclarativeAlternativeMixedModels333
