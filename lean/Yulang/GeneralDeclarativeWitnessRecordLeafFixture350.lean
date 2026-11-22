import Yulang.GeneralDeclarativeWitnessRecordReplay350
import Yulang.GeneralDeclarativeWitnessRecordFixture349

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
namespace Yulang.GeneralDeclarativeWitnessRecordLeafFixture350
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWitnessCutDecl334 (arg pat impl root)
open GeneralDeclarativeWitnessRecordFixture349 (current manifest actual wire)
open GeneralDeclarativeWitnessOneRecord350 (Anchor compilerCtx)
open GeneralDeclarativeWitnessCompiler350 (Context execute)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralSourceMetadataRows291 (Source)
open GeneralSourceMetadataBareBundle291 (InputBundle)
open GeneralSourceMetadataBundle291 (SourceBundle)
open GeneralDeclarativeWitnessHeader349 (replay)
open GeneralDeclarativeWitnessRecordReplay350 (checkLeaf leaf)
open GeneralDeclarativeEndpointCase336 (endCode)
open GeneralDeclarativeEndpointMixedTail336 (width)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeWitnessAllocation350 (next used names)
open GeneralNominalCommonBridge (Assignment)

def source : Source := ⟨.absent,[]⟩
def input : InputBundle := ⟨source,source,⟨0,[⟨1,1,[(0,none)]⟩]⟩,[impl]⟩
def answer : Report := ⟨.selected 92 [],.selected (.node 92 []),root.outputs⟩

def keep : List Nat := [19]
def fallback : Nat → GeneralDeclarativeWhere319.Capture := fun _ => arg

def baseAnchor (s : State) : Anchor :=
  ⟨⟨input,s,root⟩,current,manifest,keep,fallback,fun _ _ => 0⟩

def compiled : Option GeneralDeclarativeWitnessCompiler350.Finished := do
  let table ← replay (baseAnchor current).problem ⟨answer.outputs⟩
  let sourceRead ← GeneralDeclarativeWitnessProjection349.decode actual arg pat wire
  execute (compilerCtx (p := baseAnchor current) sourceRead table impl)

open GeneralDeclarativeEndpointCase336 (rowLo)
open GeneralDeclarativeEndpointMixedTail336 (rowHi)
open GeneralDeclarativeWitnessRecordFixture349 (center)
open GeneralDeclarativeWitnessRecordReplay350 (Wire)
abbrev ProjectionCode := GeneralDeclarativeWitnessExactRest349.Wire
open GeneralDeclarativeEntailment320 (Holds)
open CommonNominalFullCarrier (Subtype exactEmpty emptyRecord subtype_refl subtype_trans exactEmpty_below_width)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralDeclarativeRecordSplit330 (bottom interval)

def edges : List (Nat × Nat) :=
  [(20,21),(21,22),(23,24),(24,25),
   (21,21),(21,21),(26,20),(20,26),(27,22),(22,27),(26,21),(21,27),
   (24,24),(24,24),(28,23),(23,28),(29,25),(25,29),(28,24),(24,29)]

def fixed : Equation := ⟨5,.variable 21⟩
def projected : List Equation :=
  [⟨20,.variable 3⟩,⟨21,.variable 4⟩,⟨22,.variable 4⟩,
   ⟨23,endCode⟩,⟨24,endCode⟩,⟨25,width⟩]

def state : State :=
  ⟨⟨edges.map (fun (l,h) => .tyLe (.var l) (.var h)),[(0,1),(1,2)]⟩,
    [rowLo,rowHi,center,fixed] ++ projected⟩

def fieldProof : ProjectionCode :=
  ⟨[(7,.variable 4)],endCode,.currentRow 2,.currentRow 4,.currentRow 5,.currentRow 6⟩
def tailProof : ProjectionCode :=
  ⟨[(7,.variable 4)],endCode,.currentRow 2,.currentRow 7,.currentRow 8,.currentRow 9⟩

def recordWitness : Wire :=
  ⟨wire,wire,[(0,20,21,22),(1,23,24,25)],[fieldProof,tailProof],0,.same,[1,1,1],
    ⟨[],[fixed],⟨List.range 20,[.interval 0,.interval 1],(List.range 4).map .currentRow⟩⟩⟩

theorem accepted : checkLeaf (baseAnchor state) answer recordWitness = true := by decide +kernel

theorem swapped_projection_slots :
    checkLeaf (baseAnchor state) answer
      {recordWitness with slots := [(1,23,24,25),(0,20,21,22)]} = false := by decide +kernel

theorem wrong_literal_output :
    checkLeaf (baseAnchor state) answer {recordWitness with emitted :=
      {recordWitness.emitted with outputRows := [⟨5,.variable 4⟩]}} = false := by decide +kernel

theorem unavailable_upper_is_not_authorized :
    checkLeaf (baseAnchor state) answer {recordWitness with currentProjection :=
      {wire with upper := .inline 2 .same}} = false := by decide +kernel

def model : Assignment := fun n =>
  if n ∈ [20,26] then (.bottom,Common.rowEmpty)
  else if n ∈ [23,24,28] then (exactEmpty,Common.rowEmpty)
  else if n ∈ [25,29] then (emptyRecord,Common.rowEmpty)
  else if n ∈ [5,21,22,27] then (.top,Common.rowEmpty)
  else GeneralDeclarativeWitnessRecordFixture349.model n

theorem edge_fit (e : Nat × Nat) (known : e ∈ edges) :
    Subtype (model e.1).1 (model e.2).1 := by
  simp only [edges,List.mem_cons,List.not_mem_nil,or_false] at known
  rcases known with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    first | exact subtype_refl _ | exact bottom _ | exact exactEmpty_below_width

theorem fixed_state_model : Models state model := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · unfold PresenceNormalForm.All
    intro a h
    obtain ⟨e,there,rfl⟩ := List.mem_map.mp h
    exact edge_fit _ there
  · intro e listed
    change e ∈ [(0,1),(1,2)] at listed
    rcases List.mem_cons.mp listed with rfl|h
    · exact subtype_trans (interval 7).1 (interval 7).2
    · cases List.mem_singleton.mp h
      exact CommonNominalFullCarrier.common_record_mono 7 (subtype_refl _) exactEmpty_below_width
  · intro e h
    change e ∈ [rowLo,rowHi,center,fixed,
      ⟨20,.variable 3⟩,⟨21,.variable 4⟩,⟨22,.variable 4⟩,⟨23,endCode⟩,⟨24,endCode⟩,⟨25,width⟩] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact eqv_refl _

theorem nonvacuous :
    ∃ a : GeneralDeclarativeWitnessRecordReplay350.Accepted (baseAnchor state) answer recordWitness,
      Models state model ∧ GeneralDeclarativeExactDictionary337.Evidence
        (GeneralSourceMetadataBundle291.registry a.table) (GeneralSourceMetadataRows291.interpretation a.table.snapshot)
        model root (.node a.decl.id []) ∧ Holds model fixed := by
  obtain ⟨a,_,_,_,_,sound⟩ := leaf accepted
  have facts := sound model fixed_state_model
  exact ⟨a,fixed_state_model,facts.1,facts.2.2 fixed List.mem_cons_self⟩

end Yulang.GeneralDeclarativeWitnessRecordLeafFixture350
