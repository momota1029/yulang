import Yulang.GeneralDeclarativeI65I74ComputedOldPalette486
import Yulang.GeneralDeclarativeI65I74TypedRootSafety482

namespace Yulang.GeneralDeclarativeI65.I72.CandidateTape485
open RetainedFull445 (FullProblem)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open LiteralVisits473 (GuardedObservationInput Checkpoint readCheck)
open TypedRootSafety482 (AllRootSafe noRootReturnBool requestRootCheck)

def authoredRootCoordinate487 {n : Nat} (pos : Positions n) (lower : Nat) : Option (Fin n) :=
  (List.finRange n).find? fun i => decide (oldPosition pos i = .logical lower)

def computedOriginalRootCertificate487 {n : Nat} (s : GeneralDeclarativeI65.State)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (lower : Nat) : Option (Checkpoint n) := do
  let i ← authoredRootCoordinate487 pos lower
  let ck ← computeOldObservationCheckpoint486 s pos rel i
  if readCheck s pos rel (.logical lower) ck = some false then some ck else none

def computedOriginalRootCertificates487 {n : Nat} (s : GeneralDeclarativeI65.State)
    (pos : Positions n) (rel : List (Fin n × Fin n)) (lowers : List Nat) :
    Option (List (Checkpoint n)) :=
  lowers.mapM (computedOriginalRootCertificate487 s pos rel)

theorem computed_original_roots_pass_unmodified_ordered_request_root_check487
    {n : Nat} (s : GeneralDeclarativeI65.State) (pos : Positions n)
    (rel : List (Fin n × Fin n)) (lowers : List Nat) (args : List (Checkpoint n))
    (run : computedOriginalRootCertificates487 s pos rel lowers = some args) :
    noRootReturnBool s pos rel lowers args = true := by
  induction lowers generalizing args with
  | nil =>
    have exact : [] = args := Option.some.inj run
    subst args
    rfl
  | cons lower rest ih =>
    simp only [computedOriginalRootCertificates487,List.mapM_cons] at run
    cases head : computedOriginalRootCertificate487 s pos rel lower with
    | none => simp [head] at run
    | some ck =>
      cases tail : computedOriginalRootCertificates487 s pos rel rest with
      | none =>
        change rest.mapM (computedOriginalRootCertificate487 s pos rel) = none at tail
        simp [head,tail] at run
      | some cks =>
        have matchArgs : ck::cks = args := by
          simpa [head,show rest.mapM (computedOriginalRootCertificate487 s pos rel) = some cks from tail] using run
        subst args
        have checked : readCheck s pos rel (.logical lower) ck = some false := by
          unfold computedOriginalRootCertificate487 at head
          cases loc : authoredRootCoordinate487 pos lower with
          | none => simp [loc,Option.bind] at head
          | some idx =>
            cases read : computeOldObservationCheckpoint486 s pos rel idx with
            | none => simp [loc,read,Option.bind] at head
            | some w =>
              by_cases h : readCheck s pos rel (.logical lower) w = some false
              · have same : w = ck := by simpa [loc,read,Option.bind,h] using head
                exact same ▸ h
              · simp [loc,read,Option.bind,h] at head
        simp [noRootReturnBool,checked,ih cks tail]

theorem old_position_table_nodup_defines_the_exact_computed_coordinate487
    {n : Nat} (pos : Positions n) {lower : Nat} {i : Fin n}
    (unique : (List.ofFn (oldPosition pos)).Nodup)
    (actual : oldPosition pos i = .logical lower) :
    authoredRootCoordinate487 pos lower = some i := by
  let pick (x : Fin n) : Bool := decide (oldPosition pos x = .logical lower)
  have yes : pick i = true := decide_eq_true actual
  have someVal : ((List.finRange n).find? pick).isSome :=
      List.find?_isSome.mpr ⟨i,List.mem_finRange i,yes⟩
  obtain ⟨j,found⟩ : ∃ j, ((List.finRange n).find? pick) = some j := by
    cases hit : (List.finRange n).find? pick with
    | none => simp [hit] at someVal
    | some j => exact ⟨j,rfl⟩
  have rightBool : pick j = true := List.find?_some found
  have right : oldPosition pos j = .logical lower := of_decide_eq_true rightBool
  have same : j = i := by
    apply Fin.ext
    have there : j.val < (List.ofFn (oldPosition pos)).length := by simp
    have here : i.val < (List.ofFn (oldPosition pos)).length := by simp
    have equal : (List.ofFn (oldPosition pos))[j.val]'there =
        (List.ofFn (oldPosition pos))[i.val]'here := by simpa using (right.trans actual.symm)
    exact (List.Nodup.getElem_inj unique).mp equal
  change (List.finRange n).find? pick = some i
  simpa [same] using found

theorem independently_safe_guarded_root_is_computed_at_its_exact_logical_coordinate487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {i : Fin n} {lower : Nat}
    (guard : GuardedObservationInput s pos rel i)
    (actual : oldPosition pos i = .logical lower)
    (safe : ¬ ReturnsUpToEquality (graphOf s pos) i) :
    ∃ ck, computedOriginalRootCertificate487 s pos rel lower = some ck ∧ ck.which = i := by
  have located := old_position_table_nodup_defines_the_exact_computed_coordinate487 pos guard.2.1 actual
  obtain ⟨ck,cp⟩ := old_input_guards_suffice_for_computing_an_exact_checkpoint486 guard
  obtain ⟨which,bit,out⟩ := computed_old_checkpoint_is_at_its_own_original_coordinate486 cp
  have sign := (LiteralVisits473.read_checkpoint_guards out).2.2
  have isFalse : bit = false := by
    cases h : bit
    · rfl
    · exact False.elim (safe (which ▸ sign.mp h))
  rw [isFalse,actual] at out
  exact ⟨ck,by simp [computedOriginalRootCertificate487,located,cp,out,Option.bind],which⟩

theorem given_exact_old_guarded_safe_roots_the_computer_returns_all_in_same_order487
    {n : Nat} {s : GeneralDeclarativeI65.State} {pos : Positions n}
    {rel : List (Fin n × Fin n)} {lowers : List Nat} {coords : List (Fin n)}
    (exact : AllRootSafe s pos lowers coords)
    (guard : ∀ i ∈ coords, GuardedObservationInput s pos rel i) :
    ∃ checks, computedOriginalRootCertificates487 s pos rel lowers = some checks ∧
      checks.map Checkpoint.which = coords := by
  induction lowers generalizing coords with
  | nil => cases coords with
    | nil => exact ⟨[],rfl,rfl⟩
    | cons => exact False.elim exact
  | cons l ls ih =>
    cases coords with
    | nil => exact False.elim exact
    | cons j js =>
      obtain ⟨atRoot,safe,rest⟩ := exact
      obtain ⟨ck,head,loc⟩ := independently_safe_guarded_root_is_computed_at_its_exact_logical_coordinate487
        (guard j (List.mem_cons_self ..)) atRoot safe
      obtain ⟨cks,tail,same⟩ := ih rest (fun t mem => guard t (List.mem_cons_of_mem _ mem))
      exact ⟨ck::cks,by simp [computedOriginalRootCertificates487,List.mapM_cons,head,
        show ls.mapM (computedOriginalRootCertificate487 s pos rel) = some cks from tail],by simp [loc,same]⟩

end Yulang.GeneralDeclarativeI65.I72.CandidateTape485
