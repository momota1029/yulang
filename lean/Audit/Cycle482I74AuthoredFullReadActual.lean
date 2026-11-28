import Yulang.GeneralDeclarativeI65I74AuthoredFullRead482

set_option maxHeartbeats 1500000
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank.Actual
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralDeclarativeInlineTrace331 (Read)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open CommonNominalFullCarrier (record)

def wide : Expr := .primitive .emptyRecord []
def exactEnd : Expr := .primitive .exactEmpty []
def headEq : Equation := ⟨4,.record 30 (.variable 6) (.variable 9)⟩
def oldAlias : Equation := ⟨6,.variable 7⟩
def leafEq : Equation := ⟨7,wide⟩
def tailEq : Equation := ⟨9,.record 31 (.variable 8) exactEnd⟩
def before : GeneralDeclarativeHead320.State := ⟨⟨[],[]⟩,[headEq,oldAlias,leafEq,tailEq]⟩
def genuine : Table := ⟨before.equations,[],[]⟩
def pending : Table := ⟨[headEq,leafEq,tailEq],[(oldAlias,41)],[]⟩

def opens : Expr := .record 30 wide (.record 31 (.variable 61) exactEnd)
def writtenFields : List (Nat × Expr) := [(30,wide),(31,.variable 61)]
def expected : List Occurrence := [⟨61,.actual,.variable 8⟩]

def choices : ObservationAliasHead472.Catalogue :=
  [(6,⟨[(6,.same),(7,.forward 1)],⟨[],[]⟩⟩)]
def cardAt (tailAuthor leafAuthor : Nat) (known : ObservationAliasHead472.Catalogue) : ReadCard :=
  .record [⟨⟨0,0⟩,[]⟩,⟨⟨3,tailAuthor⟩,[]⟩] [30,31] writtenFields exactEnd
    (.cons (.expose ⟨⟨2,leafAuthor⟩,known⟩ (.primitive .nil))
      (.cons .capture .nil))
    (.primitive .nil)

def oneGood := cardAt 3 2 choices

def tailTy := value (fun _ _ => .emptyRecord) .actual tailEq.right
def rootTy := value (fun _ n => if n = 9 then tailTy else .emptyRecord) .actual headEq.right
def assignment : Assignment := fun n =>
  (if n = 4 then rootTy else if n = 9 then tailTy else .emptyRecord,Common.rowEmpty)

theorem genuine_c331_input_snapshot_has_an_ordinary_model : Models before assignment := by
  refine ⟨⟨fun _ h => False.elim (List.not_mem_nil h),fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro row has
  change row ∈ [headEq,oldAlias,leafEq,tailEq] at has
  simp only [List.mem_cons,List.not_mem_nil,or_false] at has
  rcases has with rfl|rfl|rfl|rfl <;> exact eqv_refl _

private def exactCapture : Option (List Occurrence) → Bool
  | some [⟨61,.actual,.variable 8⟩] => true
  | _ => false

private theorem exactCapture_sound (x : Option (List Occurrence)) (yes : exactCapture x = true) :
    x = some expected := by
  unfold exactCapture at yes
  split at yes
  · rfl
  · cases yes

theorem whole_authored_record_and_child_alias_replay_finite_card :
    runReadCard before genuine .actual (.variable 4) opens oneGood = some expected ∧
    Read (authoredView before genuine) .actual (.variable 4) opens expected := by
  have reads : runReadCard before genuine .actual (.variable 4) opens oneGood = some expected := by
    apply exactCapture_sound
    decide +kernel
  exact ⟨reads,runReadCard_sound reads⟩

/-- info: [true, false, false, false] -/
#guard_msgs in
#eval [
  (runReadCard before genuine .actual (.variable 4) opens oneGood).isSome,
  (runReadCard before pending .actual (.variable 4) opens (cardAt 2 1 choices)).isSome,
  (runReadCard before genuine .actual (.variable 4) opens (cardAt 3 2 [])).isSome,
  (runReadCard before genuine .actual (.variable 4)
    (.record 30 wide (.record 31 (.variable 62) exactEnd)) oneGood).isSome]

#print axioms genuine_c331_input_snapshot_has_an_ordinary_model
#print axioms whole_authored_record_and_child_alias_replay_finite_card
end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank.Actual
