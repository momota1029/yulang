import Yulang.GeneralDeclarativeI65I74PreviousOrdinaryMaterialBoundary465

set_option backward.isDefEq.respectTransparency false
namespace Yulang.OrdinaryOccurrenceStamp466
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeInlineAllocation331 (jobs)
open GeneralDeclarativeRecordPoints330 (expanded)
open GeneralDeclarativeNewNames321 (numbered supply)
open GeneralDeclarativeInlineMaterial331 (ordinary seed)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def taggedParts (n : Nat) : List Occurrence → List (Nat × Occurrence)
  | [] => []
  | first::rest =>
    (expanded first.term).map (fun _ => (n,first)) ++ taggedParts (n+1) rest

theorem job_ordinals_preserve_exact_existing_rhs_sequence
    (n : Nat) (found : List Occurrence) :
    (taggedParts n found).map (fun p => p.2.term) = jobs found := by
  induction found generalizing n with
  | nil => rfl
  | cons f rest ih =>
    have head : ((expanded f.term).map (fun _ => (n,f))).map (fun p => p.2.term) = expanded f.term := by
      cases f with
      | mk binder mode term => cases term <;> rfl
    rw [taggedParts,List.map_append,head,ih]
    rfl

theorem tagged_job_is_the_literal_input_capture_and_not_a_variable
    {off index : Nat} {found : List Occurrence} {original : Occurrence}
    (hit : (off+index,original) ∈ taggedParts off found) :
    found[index]? = some original ∧ ∀ j, original.term ≠ .variable j := by
  induction found generalizing off index with
  | nil => simp [taggedParts] at hit
  | cons f later ih =>
    rw [taggedParts,List.mem_append] at hit
    rcases hit with first|rest
    · obtain ⟨rhs,active,eq⟩ := List.mem_map.mp first
      have p0 : 0 = index := by
        have address : off = off + index := congrArg Prod.fst eq
        omega
      have same : f = original := congrArg Prod.snd eq
      subst index
      subst original
      refine ⟨rfl,?_⟩
      intro j contradiction
      rw [contradiction] at active
      cases active
    · have bound : ∀ k o, (k,o) ∈ taggedParts (off+1) later → off+1 ≤ k := by
        intro k o hh
        clear rest ih
        generalize startEq : off+1 = start at hh ⊢
        clear startEq
        induction later generalizing start with
        | nil => simp [taggedParts] at hh
        | cons f rest ih =>
          rw [taggedParts,List.mem_append] at hh
          rcases hh with head|tail
          · obtain ⟨_,_,eq⟩ := List.mem_map.mp head
            exact Nat.le_of_eq (congrArg Prod.fst eq)
          · have later := ih (start+1) tail
            omega
      have nPos := bound _ _ rest
      cases index with
      | zero => simp at nPos; omega
      | succ k =>
        have normal : off + (k + 1) = off + 1 + k := by omega
        change (off + (k + 1),original) ∈ _ at rest
        rw [normal] at rest
        exact ih rest

theorem actual_old_numbered_row_uses_its_consecutive_raw_target
    (start : Nat) (exps : List Expr) (i : Nat) :
    (numbered start exps)[i]? = (exps[i]?).map (fun e => (⟨start+i,e⟩ : Equation)) := by
  induction exps generalizing start i with
  | nil => rfl
  | cons e later ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp [numbered,ih,Nat.add_assoc,Nat.add_comm 1 i]

def existingCaptureJob (s : State) (a : Capture) (keep : List Nat)
    (found : List Occurrence) (position : Nat) : Option (Nat × Nat × Occurrence) :=
  ((taggedParts 0 found)[position]?).map (fun k => (seed s a keep found + position,k.1,k.2))

theorem successful_ordinal_reads_original_capture_and_allocated_row
    (s : State) (a : Capture) (keep : List Nat) (used : List Occurrence)
    {i target source : Nat} {found : Occurrence}
    (read : existingCaptureJob s a keep used i = some (target,source,found)) :
    used[source]? = some found ∧ (∀ n, found.term ≠ .variable n) ∧
      (ordinary s a keep used)[i]? = some ⟨target,found.term⟩ := by
  cases selected : (taggedParts 0 used)[i]? with
  | none => simp [existingCaptureJob,selected] at read
  | some pair =>
    obtain ⟨k,actual⟩ := pair
    simp [existingCaptureJob,selected] at read
    obtain ⟨rfl,rfl,rfl⟩ := read
    have seen := List.mem_of_getElem? selected
    have exactSource := tagged_job_is_the_literal_input_capture_and_not_a_variable
      (off := 0) (index := k) (by simpa using seen)
    have row : (jobs used)[i]? = some actual.term := by
      rw [←job_ordinals_preserve_exact_existing_rhs_sequence 0 used]
      simp [List.getElem?_map,selected]
    have eq : (ordinary s a keep used)[i]? = some ⟨seed s a keep used+i,actual.term⟩ := by
      change (numbered (seed s a keep used) (jobs used))[i]? = _
      rw [actual_old_numbered_row_uses_its_consecutive_raw_target,row]
      rfl
    exact ⟨exactSource.1,exactSource.2,eq⟩

theorem no_created_ordinary_row_is_lost_by_the_ordinal_adapter
    (s : State) (a : Capture) (keep : List Nat) (used : List Occurrence) (i : Nat) :
    (existingCaptureJob s a keep used i).map (fun x => (⟨x.1,x.2.2.term⟩ : Equation)) =
      (ordinary s a keep used)[i]? := by
  change _ = (numbered (seed s a keep used) (jobs used))[i]?
  rw [actual_old_numbered_row_uses_its_consecutive_raw_target,
      ← job_ordinals_preserve_exact_existing_rhs_sequence 0 used]
  unfold existingCaptureJob
  cases picked : (taggedParts 0 used)[i]? <;> simp [List.getElem?_map,picked]

open GeneralDeclarativeNestedMaterial332 (assemble)
open GeneralDeclarativeNestedRebuild332 (rebuild)
open GeneralDeclarativeInlineMaterial331 (named)
open GeneralDeclarativeInlineAllocation331 (renamed captures)
open GeneralDeclarativeEntailment320 (appendFacts)

theorem actual_legacy_assembly_places_the_old_ordinary_inputs_before_named_jobs
    {s : State} {a fixed code used result names}
    (actual : assemble s a fixed code used = some (result,names)) :
    ∃ head, result.equations = (s.equations ++ ordinary s a fixed used) ++ [⟨a.center,head⟩] := by
  unfold assemble at actual
  cases rebuilt : rebuild code (renamed (seed s a fixed used) used) with
  | none => simp [rebuilt,Option.bind] at actual
  | some made =>
    obtain ⟨body,leftover⟩ := made
    simp [rebuilt,Option.bind] at actual
    obtain ⟨_,rfl,_⟩ := actual
    exact ⟨body,rfl⟩

theorem actual_allocation_receipt_links_exact_old_capture_to_exact_new_raw_ordinal
    {s : State} {a fixed code used result names target source i found}
    (actual : assemble s a fixed code used = some (result,names))
    (chosen : existingCaptureJob s a fixed used i = some (target,source,found)) :
    used[source]? = some found ∧
      result.equations[s.equations.length + i]? = some ⟨target, found.term⟩ := by
  obtain ⟨sourceAt,_,rowAt⟩ := successful_ordinal_reads_original_capture_and_allocated_row
      s a fixed used chosen
  obtain ⟨body,rows⟩ := actual_legacy_assembly_places_the_old_ordinary_inputs_before_named_jobs actual
  have inside : i < (ordinary s a fixed used).length := by
    by_cases positive : i < (ordinary s a fixed used).length
    · exact positive
    · have absent : (ordinary s a fixed used)[i]? = none := List.getElem?_eq_none (by omega)
      rw [rowAt] at absent
      contradiction
  refine ⟨sourceAt,?_⟩
  rw [rows,List.append_assoc,
      List.getElem?_append_right (Nat.le_add_right ..),Nat.add_sub_cancel_left,
      List.getElem?_append_left inside,rowAt]

end Yulang.OrdinaryOccurrenceStamp466
