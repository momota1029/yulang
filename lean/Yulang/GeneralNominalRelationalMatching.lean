import Yulang.GeneralNominalInspectionMatching

/-! Recursive matching with an arbitrary interpretation of captured variables.
The raw and centered producers supply their own capture callbacks. -/
namespace Yulang.GeneralNominalRelationalMatching
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalReadbackFunctionality
open GeneralNominalGroundAccessibility GeneralNominalMatchedAssembly GeneralNominalHeadMatchMass
open GeneralNominalSharedCaptures GeneralNominalSaturationState
open GeneralNominalInspectionAlignment GeneralNominalInspectionPositions
open GeneralNominalInspectionFiniteValues

variable {relation : Nat → Expr Nat → Prop}

mutual
  theorem inspect_matched (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
      (valid : GeneralNominalState.Models packet.context.state model)
      (captures : List (Capture packet.context.state))
      (captureValue : ∀ captured ∈ captures, ∀ term,
        Input context model packet.context.state captured.bounds captured.origin term → relation captured.name term) (query : Query) (bounds : Bounds packet.context.state)
      (origin : Option Origin) (term : Expr Nat) (single : Single query)
      (finished : Finished (inspect packet.context.state query bounds origin))
      (known : Input context model packet.context.state bounds origin term)
      (included : (inspect packet.context.state query bounds origin).captures ⊆ captures) :
      Matches relation query term := by
    cases query with
    | variables names =>
      simp only [Single] at single
      obtain ⟨name,rfl⟩ := single
      apply Matches.capture
      exact captureValue ⟨name,bounds,origin⟩
        (included (by simp [inspect])) term known
    | deferred => simp only [inspect,Finished,block] at finished; cases finished.1
    | scalar base =>
      simp only [inspect,finished_visit] at finished
      split at finished
      · simp only [Finished] at finished; cases finished.2.1
      · split at finished
        · rename_i actual recorded
          split at finished
          · rename_i same
            obtain ⟨pattern,closed⟩ := known.1
            have equal := scalar_slot packet.context.state model valid bounds.1 recorded
            rw [← same] at equal
            obtain ⟨children,identical⟩ := scalar_finite term closed.2.1 (CommonNominalFullCarrier.subtype_trans equal.2 known.2.1.1)
            rw [identical]
            exact .scalar children
          · simp only [Finished] at finished; cases finished.2.1
        · simp only [Finished] at finished; cases finished.2.1
        · simp only [Finished,block] at finished; cases finished.1
    | node shape queries =>
      simp only [Single] at single
      simp only [inspect,finished_visit] at finished
      split at finished
      · rename_i lowerKind lower upperKind upper lowerAt upperAt
        split at finished
        · rename_i same
          obtain ⟨children,equal,childInputs⟩ := structural_inputs packet.context.state model valid bounds
            lowerKind upperKind lower upper lowerAt upperAt same.1 same.2 known
          have childIncluded : (inspectMany packet.context.state queries ((List.ofFn lower).zip (List.ofFn upper))
              (fun index => origin.map fun parent => .structural parent shape index) 0).captures ⊆ captures := by
            simpa only [inspect,lowerAt,upperAt,same,and_self,ite_true,Report.visit] using included
          have matched := many_matched packet model valid captures captureValue queries _ _ 0 _ single finished childInputs childIncluded
          have length := finished_length packet.context.state queries _ _ 0 finished
          rw [zip_reindex same.1 same.2,List.length_ofFn] at length
          rw [equal]
          exact structural_matched matched length
        · simp only [Finished,block] at finished; cases finished.1
      · simp only [Finished] at finished; cases finished.2.1
      · simp only [Finished,block] at finished; cases finished.1
    | nominal name queries =>
      simp only [Single] at single
      obtain ⟨descriptor,intervals,recorded,same,found,complete,subset⟩ := nominal_left packet.context.state queries bounds origin finished
      obtain ⟨children,equal,childInputs⟩ := nominal_inputs packet.context.state model valid bounds descriptor recorded found known
      rw [same] at equal childInputs
      have matched := many_matched packet model valid captures captureValue queries intervals _ 0 _ single complete childInputs
        (fun _ member => included (subset member))
      rw [equal]
      exact nominal_matched matched (finished_length packet.context.state queries intervals _ 0 complete)
    termination_by sizeOf query

  theorem many_matched (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
      (valid : GeneralNominalState.Models packet.context.state model)
      (captures : List (Capture packet.context.state))
      (captureValue : ∀ captured ∈ captures, ∀ term,
        Input context model packet.context.state captured.bounds captured.origin term → relation captured.name term) (queries : List Query) (bounds : List (Bounds packet.context.state))
      (origins : Nat → Option Origin) (offset : Nat) (terms : List (Expr Nat))
      (single : ∀ query ∈ queries, Single query)
      (finished : Finished (inspectMany packet.context.state queries bounds origins offset))
      (known : InputsAt context model packet.context.state origins offset bounds terms)
      (included : (inspectMany packet.context.state queries bounds origins offset).captures ⊆ captures) :
      Aligned (Matches relation) queries terms := by
    cases queries with
    | nil =>
      cases bounds with
      | nil => cases terms with
        | nil => exact .nil
        | cons => cases known
      | cons => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons query rest =>
      cases bounds with
      | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
      | cons bounds tail =>
        cases terms with
        | nil => cases known
        | cons term terms =>
          simp only [inspectMany,finished_append] at finished
          simp only [inspectMany,Report.append] at included
          refine .cons (inspect_matched packet model valid captures captureValue query bounds (origins offset) term
            (single query (List.mem_cons_self ..)) finished.1 known.1
            (fun _ member => included (List.mem_append_left _ member))) ?_
          exact many_matched packet model valid captures captureValue rest tail origins (offset+1) terms
            (fun q member => single q (List.mem_cons_of_mem _ member)) finished.2 known.2
            (fun _ member => included (List.mem_append_right _ member))
    termination_by sizeOf queries
end

theorem actual_capture (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (branch : packet.Holds model) (generation : GenerationGuard tracked packet)
    (captured : Capture packet.context.state) (member : captured ∈ (inheritedReport packet).captures)
    (term : Expr Nat) (known : Input context model packet.context.state captured.bounds captured.origin term) :
    CapturedPart context packet model captured.name term := by
  have matched : Matches (CapturedPart context packet model) (.variables [captured.name]) term :=
    variable_match packet model branch generation known (by
      intro other present
      have equal : other = captured := by simpa only [inspect,List.map_cons,List.map_nil,List.mem_singleton] using present
      exact equal ▸ member)
  cases matched with
  | capture part => exact part

theorem actual_many_matched (packet : Packet roles) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models packet.context.state model)
    (branch : packet.Holds model) (generation : GenerationGuard tracked packet)
    (queries : List Query) (bounds : List (Bounds packet.context.state))
    (origins : Nat → Option Origin) (offset : Nat) (terms : List (Expr Nat))
    (single : ∀ query ∈ queries, Single query)
    (finished : Finished (inspectMany packet.context.state queries bounds origins offset))
    (known : InputsAt context model packet.context.state origins offset bounds terms)
    (included : (inspectMany packet.context.state queries bounds origins offset).captures ⊆ (inheritedReport packet).captures) :
    Aligned (Matches (CapturedPart context packet model)) queries terms :=
  many_matched packet model valid (inheritedReport packet).captures
    (actual_capture packet model branch generation) queries bounds origins offset terms single finished known included

end Yulang.GeneralNominalRelationalMatching
