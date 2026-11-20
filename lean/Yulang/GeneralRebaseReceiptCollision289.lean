import Yulang.GeneralRebaseReceiptExtractLaws289

/-! A checked registry can have the same finite declarations yet differ
in constructor metadata. Do not infer arbitrary current Frame from the
first recorder merely because the wire is accepted. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptCollision289
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseReceiptFixture289 (wire request endpoint_decision)
open GeneralRebaseReceiptExtract289 (extract)
open GeneralRebaseReceiptWire289 (check)
open GeneralNominalVersionedEvidence231 (Frame)

def removed (key : Nat) : Registry :=
  { registry true with constructors := fun i => if i = key then none else constructors i }

theorem removed_checked (key : Nat) (notParent : key ≠ 0) : Checked (removed key) := by
  refine ⟨(checked true).1,?_⟩
  intro d visible
  change d ∈ [parentDecl,opaqueChild] at visible
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  have keep : ¬ (0 : Nat) = key := Ne.symm notParent
  rcases visible with rfl | rfl
  · refine ⟨parent_checked.signature,parent_checked.identified,parent_checked.produced,
      parent_checked.outputOnly,parent_checked.scope,?_,parent_checked.countsCovered,
      parent_checked.paterson,parent_checked.conservative,parent_checked.captureStable⟩
    simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,removed,keep,constructors]
  · refine ⟨opaque_checked.signature,opaque_checked.identified,opaque_checked.produced,
      opaque_checked.outputOnly,opaque_checked.scope,?_,opaque_checked.countsCovered,
      opaque_checked.paterson,opaque_checked.conservative,opaque_checked.captureStable⟩
    simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]

theorem original_catalogue_present (key : Nat) : (constructors key).isSome = true := by
  simp [constructors,GeneralDeclarationExamples.constructors]
  split <;> rfl

theorem no_current_frame (key which : Nat) (p : GeneralNominalCenters.Plan roles) :
    ¬ Frame (removed key) (after true).core (child true) which p := by
  intro frame
  have metadata := frame.prepared.1.1
  have atKey := congrFun metadata key
  change (if key = key then none else constructors key) = constructors key at atKey
  rw [ite_eq_left rfl] at atKey
  have means := congrArg Option.isSome atKey
  rw [original_catalogue_present] at means
  cases means

theorem declarations_only_collision (key : Nat) :
    check (extract (removed key) (after true) (child true)) (request true) = .ready :=
  endpoint_decision true

theorem checked_collision :
    Checked (removed 6) ∧
      check (extract (removed 6) (after true) (child true)) (request true) = .ready ∧
      ∀ key p, ¬ Frame (removed 6) (after true).core (child true) key p :=
  ⟨removed_checked 6 (by decide),declarations_only_collision 6,no_current_frame 6⟩

end Yulang.GeneralRebaseReceiptCollision289
