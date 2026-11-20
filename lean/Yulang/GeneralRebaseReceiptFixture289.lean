import Yulang.GeneralRebaseReceiptExtract289

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 19000000
namespace Yulang.GeneralRebaseReceiptFixture289
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287 (child plan sole_child)
open GeneralRebaseRowParentFrame287 (after effect before_requests)
open GeneralRebaseRowGeneratedChild287 (current current_args)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseReceiptWire289
open GeneralRebaseReceiptExtract289

abbrev request (choice : Bool) : Offer :=
  ⟨(registry choice).declarations,root.identity,0,(child choice).identity,1,2⟩

abbrev producer (choice : Bool) : Producer :=
  ⟨(registry choice).declarations,root.identity,0,[(child choice).identity],[2]⟩

theorem producer_exact (choice : Bool) : effectSummary (effect choice) = producer choice := by
  unfold effectSummary
  change Producer.mk _ _ _ ((_: List _).map _) ((_: List _).map _) = _
  have kids := sole_child choice
  have req := before_requests
  dsimp only [effect,producer]
  rw [kids,GeneralRebaseExecutableRequests262.requests_eq,show (GeneralNominalDemandMerging.pointSite root).occurrence = root from rfl,req]
  rfl

theorem candidates_exact (choice : Bool) :
    candidates (registry choice) (child choice) = [childDecl choice] := by
  cases choice <;> decide +kernel

theorem no_targets (choice : Bool) :
    GeneralRebaseExecutableRequests262.requests (after choice).core (child choice) = [] := by
  cases choice <;> decide +kernel

theorem root_recorded (choice : Bool) : rootRecorded (current choice) (child choice) = true := by
  unfold rootRecorded
  rw [current_args choice]
  rfl

def actualReport (choice : Bool) : Inspection := ⟨!choice,false,false⟩

theorem diagnostic_exact (choice : Bool) :
    diagnostic (current choice) (child choice) (childDecl choice) = some (actualReport choice) := by
  cases choice <;> decide +kernel

noncomputable def wire (choice : Bool) (state : State roles) : Wire :=
  extract (registry choice) state (child choice)

def expectedWire (choice : Bool) : Wire :=
  ⟨(registry choice).declarations,[producer choice],[(root.identity,(child choice).identity)],
    (child choice).identity,[childDecl choice],[],true,some (actualReport choice)⟩

theorem wire_exact (choice : Bool) : wire choice (after choice) = expectedWire choice := by
  unfold wire extract expectedWire
  change Wire.mk _ (([effect choice] : List _).map effectSummary)
    (((after choice).core.erased.current.edges).map _) _ _ _ _ _ = _
  rw [GeneralRebaseRowClosure287.edges,candidates_exact,no_targets]
  change Wire.mk _ [effectSummary (effect choice)] _ _ _ _
    (rootRecorded (current choice) (child choice))
    (diagnostic (current choice) (child choice) (childDecl choice)) = _
  rw [producer_exact,root_recorded,diagnostic_exact]
  rfl

theorem initial_no_producer (choice : Bool) :
    check (wire choice before) (request choice) = .missingProducer := by
  unfold check
  have worlds : (wire choice before).world = (request choice).world := rfl
  have list : (wire choice before).producers = [] := rfl
  simp [worlds,list]

theorem producer_matches (choice : Bool) : (producer choice).matches (request choice) = true := by
  apply (matching_producer _ _).mpr
  exact ⟨rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _⟩

theorem expected_decision (choice : Bool) :
    check (expectedWire choice) (request choice) = (if choice then .ready else .unfinished) := by
  have producers : (expectedWire choice).producers.any (·.matches (request choice)) = true :=
    List.any_eq_true.mpr ⟨producer choice,List.mem_singleton_self _,producer_matches choice⟩
  have world : (expectedWire choice).world = (request choice).world := rfl
  have identity : (expectedWire choice).child = (request choice).child := rfl
  have edge : ((request choice).parent,(request choice).child) ∈ (expectedWire choice).edges :=
    List.mem_singleton_self _
  unfold check
  rw [ite_eq_right (fun h => h world)]
  simp only [producers,Bool.not_true,Bool.false_eq_true,ite_false,identity,edge,ne_eq,not_true_eq_false,or_self]
  cases choice <;> rfl

theorem endpoint_decision (choice : Bool) :
    check (wire choice (after choice)) (request choice) = (if choice then .ready else .unfinished) := by
  rw [wire_exact,expected_decision]

end Yulang.GeneralRebaseReceiptFixture289
