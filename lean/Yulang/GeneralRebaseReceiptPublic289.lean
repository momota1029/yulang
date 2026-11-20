import Yulang.GeneralRebaseReceiptPoint289

/-! Exact public meaning of a released point and its canonical completion.
This is not a change to the original snapshot or direct row-pattern read. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28800
set_option maxHeartbeats 18500000
namespace Yulang.GeneralRebaseReceiptPublic289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentFrame287 (after after_exact)
open GeneralRebaseRowChildRaw287 (SourceCheck OutputCheck complete_check exact_source)
open GeneralRebaseRowParentOutput287 (replaceOutput completion_rows completion_types)
open GeneralRebaseRowLeafWitness288 (source_exact)
open GeneralRebaseReceiptCompile289 (Mark actualMark observe)
open GeneralRebaseReceiptPoint289 (release_exact)
open GeneralRebaseReceiptRawProduct289 (Config Next initial)
open GeneralRebaseRowMinimal287 (Determines missed_type type_mismatch)
open GeneralRebaseInertLeaf288 (SourceSlice)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonNominalFullCarrier (Equivalent subtype_refl subtype_trans nominal_regular_invariant_exact)

theorem adds_exact_output (m : Assignment) :
    SourceCheck m ∧ actualMark.Holds m ↔ OutputCheck m := by
  constructor
  · rintro ⟨source,mark⟩
    have lifted : Equivalent (F (m 1).1) (F (F (m 0).1)) :=
      GeneralNominalCenteredHeadMatCompilerSemantics.nominal_congr 0 (.cons source.2 .nil)
    exact ⟨source,subtype_trans mark.1 lifted.1,subtype_trans lifted.2 mark.2⟩
  · intro good
    exact ⟨good.1,GeneralRebaseReceiptPoint289.checked_slice_entails m
      ((GeneralRebaseRowLeafSlice288.slice_exact true m).mpr good)⟩

theorem exact_raw_gate (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (code : Mark)
    (released : observe root s.phase = some code) (m : Assignment) :
    Models s.raw m ↔ SourceSlice s.raw m ∧ code.Holds m := by
  obtain ⟨_,rawEq,_,rfl⟩ := (release_exact choice path code).mp released
  rw [rawEq,after_exact,source_exact]
  exact (adds_exact_output m).symm

theorem canonical_dictionary (choice : Bool) {s : Config}
    (path : B4Target.Steps (Next choice) initial s) (code : Mark)
    (released : observe root s.phase = some code) (m : Assignment) (p : Payload) :
    Models s.raw (replaceOutput m) ∧ Evidence (registry choice) s.raw.core (replaceOutput m) root p ↔
      SourceSlice s.raw m ∧ p = .node 0 [.node 1 []] := by
  obtain ⟨yes,rawEq,_,rfl⟩ := (release_exact choice path code).mp released
  subst choice
  rw [rawEq,GeneralRebaseRowPayloadExact287.exact,complete_check,source_exact]

theorem preserves_all_rows (m : Assignment) :
    (∀ n, (replaceOutput m n).2 = (m n).2) ∧
    (∀ n, n ≠ 2 → (replaceOutput m n).1 = (m n).1) :=
  ⟨completion_rows m,completion_types m⟩

theorem minimal_typed_mark (types rows : List Nat) :
    Determines types rows actualMark.Holds ↔ 1 ∈ types ∧ 2 ∈ types := by
  have same : actualMark.Holds = (GeneralRebaseRowOutputHeadSupport288.markedRead
    GeneralRebaseRowLedger288.old_refresh).Holds :=
    funext (fun m => propext (GeneralRebaseRowOutputHeadSupport288.exact_read _ m).symm)
  rw [same]
  exact GeneralRebaseRowOutputHeadSupport288.no_private_or_row_read _ types rows

theorem sidecar_reads_no_ambient_row (a b : Assignment)
    (agree : ∀ n, (a n).1 = (b n).1) : actualMark.Holds a ↔ actualMark.Holds b := by
  apply (minimal_typed_mark [1,2] []).mpr ⟨by simp,by simp⟩
  exact ⟨fun n _ => agree n,by simp⟩

end Yulang.GeneralRebaseReceiptPublic289
