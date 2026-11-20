import Yulang.GeneralSourceMetadataValidation291

/-! Explicit source rows provide cycle-290 overlay evidence. An attachment
to an existing raw state is an independent proof, not a receipt side effect. -/
namespace Yulang.GeneralSourceMetadataExport291
open GeneralDeclarations (Registry)
open GeneralNominalCandidates (Context Metadata)
open GeneralSourceMetadataRows291
open GeneralSourceMetadataValidation291 (Valid primitive_compatible)
open GeneralObservedMetadataOverlay290 (Data Represented closed_world_iff)
open GeneralObservedMetadataScope290 (certify)

def exportPair (declared recorded : Source) : Data :=
  ⟨declared.fallback.decode,constructorRows declared,constructorRows recorded,primitiveRows recorded⟩

structure Attached (declared recorded : Source) (r : Registry) (ctx : Context) : Prop where
  sharedDefault : declared.fallback = recorded.fallback
  declaredCorrect : r.constructors = constructors declared
  snapshotCorrect : ctx.state.constructors = constructors recorded
  interpretationCorrect : ctx.interpretation = interpretation recorded

theorem representation {declared recorded : Source} {r : Registry} {ctx : Context}
    (known : Attached declared recorded r ctx) : Represented r ctx (exportPair declared recorded) := by
  refine ⟨known.declaredCorrect,?_,?_⟩
  · rw [known.snapshotCorrect]
    unfold exportPair constructors
    rw [known.sharedDefault]
  · rw [known.interpretationCorrect]
    rfl

theorem completed_check_iff {declared recorded : Source} {r : Registry} {ctx : Context}
    (known : Attached declared recorded r ctx) (scope : List Nat) :
    Metadata r ctx ↔
      certify ((exportPair declared recorded).extended scope) r.constructors ctx.interpretation
        ctx.state.constructors ctx.interpretation = .good :=
  closed_world_iff r ctx _ scope (representation known)

theorem identical_checked_metadata {src : Source} {r : Registry} {ctx : Context}
    (known : Attached src src r ctx) (valid : Valid src) : Metadata r ctx := by
  unfold Metadata
  rw [known.interpretationCorrect,known.declaredCorrect]
  exact ⟨known.snapshotCorrect.symm,primitive_compatible src valid⟩

end Yulang.GeneralSourceMetadataExport291
