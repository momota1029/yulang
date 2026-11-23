import Yulang.GeneralDeclarativeWitnessClosedRecordLocal358

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 62000
set_option maxHeartbeats 90000000
namespace Yulang.GeneralDeclarativeWitnessClosedRecordFixture358
open GeneralDeclarativeWitnessClosedRecordLocal358 (read closed same_model)
open GeneralDeclarativeWitnessSharedTailProjection358 (Range rows)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source links)
open GeneralDeclarativeWitnessRecursiveSeed358 (parent outer inner plan)
open GeneralDeclarativeWitnessJoinedFixture357 (root written here)
open GeneralDeclarativeWitnessJoinedCheck357 (Layout replay)
open GeneralDeclarativeWitnessCoverageFixture357 (catalog prepare)
open GeneralDeclarativeWitnessDeclaredState357 (Current context point pointSpans)
open GeneralDeclarativeWitnessCompiler350 (Wire Finished execute printDemand)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataBareBundle291 (InputBundle)

def clause : Declaration :=
  ⟨96,6,[.record 7 (.var 33) (.var 34)],[],[⟨97,0,.record 7 (.var 33) (.var 34)⟩],[]⟩

def bundle : InputBundle :=
  ⟨⟨.absent,catalog⟩,⟨.absent,catalog⟩,
    ⟨0,[⟨5,1,[(0,none)]⟩,⟨6,1,[(0,none)]⟩]⟩,[parent,clause]⟩

def receipt : Range := ⟨7,7,8,1,2,0,outer,inner⟩
def author : Source := ⟨closed 0 :: rows receipt⟩
def base : State := ⟨⟨links inner,[]⟩,author.authored⟩

def firstLayout : Layout := ⟨base,[0,1,2,3,4,5,7,8,10,17,18,20,41,60],point,fun _ _ => 41⟩
def laterLayout (first : Finished) : Layout :=
  ⟨first.state,[0,1,2,3,4,5,7,8,10,17,18,20,41,60,63,64],point,fun _ _ => 0⟩

structure Data where
  current : Current
  first : Finished
  reached : Demand
  parentAnswer : Wire
  ownAnswer : Wire

def data : Option Data := do
  let e ← prepare bundle
  let source : Current := ⟨e,base,here⟩
  let f ← execute (context source root parent firstLayout.named (pointSpans 31 32 10)
    firstLayout.keep firstLayout.fallback firstLayout.via)
  let [d] := f.kids | none
  let l := laterLayout f
  let g ← execute (context source d clause l.named [(33,inner),(34,point 0)] l.keep l.fallback l.via)
  pure ⟨⟨e,g.state,here⟩,f,d,plan f g.state,plan g g.state⟩

def test (src : Source := author) (field tail : Nat := 33) : Bool :=
  (data.map fun a => (replay a.current root written firstLayout a.parentAnswer).isSome &&
    (read src a.current a.reached receipt field tail (laterLayout a.first) a.ownAnswer).isSome &&
    GeneralDeclarativeWitnessModeDeclaration357.ready a.current &&
    GeneralDeclarativeWitnessModeCoverage357.check a.current.environment &&
    GeneralSourceMetadataRoles291.check a.current.environment.source.roles).getD false

theorem actual_closed_record_child : test author 33 34 = true := by decide +kernel
theorem current_empty_tail_not_enough_without_author : test ⟨rows receipt⟩ 33 34 = false := by decide +kernel
theorem no_swap_field_and_tail : test author 34 33 = false := by decide +kernel

theorem physical_where_child_unchanged : data.map (fun d => printDemand d.reached) =
    some (6,[(63,10,64)],[(0,41)]) := rfl

theorem actual_record_output_written : data.map (fun d => d.ownAnswer.outputRows) =
    some [⟨41,.record 7 (.variable 4) (.variable 0)⟩] := rfl

end Yulang.GeneralDeclarativeWitnessClosedRecordFixture358
