import Yulang.GeneralRebaseReceiptStampedProduct289

/-! Runtime stamps from the exact bounded raw nominal footprint. A synthetic
row-port edit and an unrelated added point are conservative rejection tests,
not claims that those edits occurred on the original raw path. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29200
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseReceiptStampFixtures289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowGeneratedChild287 (current)
open GeneralRebaseRowSemanticMark287 (marked)
open GeneralRebaseReceiptTypedStamp289 (HeadCode Port Stamp capture heads)
open GeneralRebaseReceiptStampMachine289 (Phase step erase stale_exact)
open GeneralRebaseReceiptFixture289 (request expectedWire wire)
open GeneralRebaseReceiptStampedProduct289 (currentStamp)

def normalizedHeads : List HeadCode :=
  [⟨0,6,6,[.row 0 0]⟩,⟨1,0,0,[.type 0 0]⟩]

theorem source_heads : heads raw = normalizedHeads := by decide +kernel

theorem actual_heads (choice : Bool) : heads (current choice).state = normalizedHeads := by
  cases choice <;> decide +kernel

def normalizedStamp (choice : Bool) : Stamp := capture raw root (child choice) (request choice)

theorem same_extracted_stamp (choice : Bool) :
    currentStamp choice (after choice) = normalizedStamp choice := by
  unfold currentStamp normalizedStamp capture
  rw [show heads (after choice).core.erased.current.context.state = normalizedHeads from actual_heads choice,
    source_heads]

def wrongRow : Stamp :=
  { normalizedStamp true with snapshot := [⟨0,6,6,[.row 1 1]⟩,⟨1,0,0,[.type 0 0]⟩] }

theorem same_offer_wrong_row :
    wrongRow.offer = (normalizedStamp true).offer ∧ wrongRow ≠ normalizedStamp true := by
  refine ⟨rfl,?_⟩
  intro eq
  have different := congrArg Stamp.snapshot eq
  rw [show (normalizedStamp true).snapshot = normalizedHeads from source_heads] at different
  cases different

theorem wrong_row_stale :
    step (normalizedStamp true)
      (GeneralRebaseReceiptMachine289.tick (expectedWire true) (request true)) (.held wrongRow) =
        some (.stopped .stale) :=
  stale_exact _ _ _ same_offer_wrong_row.2

theorem same_row_stamp_accepted :
    step (normalizedStamp true)
      (GeneralRebaseReceiptMachine289.tick (expectedWire true) (request true)) (.held (normalizedStamp true)) =
        some (.sent (normalizedStamp true)) := by
  have ready := GeneralRebaseReceiptFixture289.expected_decision true
  simp [step,GeneralRebaseReceiptMachine289.tick,ready,GeneralRebaseReceiptStampMachine289.lift,
    normalizedStamp,capture]

theorem mark_footprint : heads (marked true) = normalizedHeads ++ [⟨2,0,0,[.type 1 1]⟩] := by
  decide +kernel

theorem added_point_invalidates_full_stamp :
    capture (marked true) root (child true) (request true) ≠ normalizedStamp true := by
  intro same
  have count := congrArg (fun s : Stamp => s.snapshot.length) same
  change (heads (marked true)).length = (heads raw).length at count
  rw [mark_footprint,source_heads] at count
  cases count

def describe : Option Phase → String
  | some (.sent _) => "published"
  | some (.held _) => "receipt"
  | some (.stopped .stale) => "stale-typed-stamp"
  | some (.stopped (.denied d)) => GeneralRebaseReceiptRuntime289.decisionLabel d
  | some .scan => "scan"
  | none => "none"

def exampleRun : List String :=
  let rawCheck := GeneralRebaseReceiptMachine289.tick (expectedWire true) (request true)
  [describe (step (normalizedStamp true) rawCheck (.held (normalizedStamp true))),
   describe (step (normalizedStamp true) rawCheck (.held wrongRow))]
end Yulang.GeneralRebaseReceiptStampFixtures289
