import Yulang.GeneralDeferredLadderReindexed302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralDeferredLadderCompiler302
open GeneralDeferredLadderLedger302 (Phase env)
open GeneralDeferredLadderReport302 (context display_report list_as_int)
open GeneralDeferredLadderRefresh302 (promotedPhase)
open GeneralDeferredLadderReindexed302 (probe_list_after probe_scalar_after promoted_raw_row promoted_attachment)
open GeneralObservedLadderReport301 (point)
open GeneralObservedLadderRoute301 (focus site)
open GeneralObservedLadderJournalRows301 (rawRow attached)
open GeneralObservedLadderJournalCompiler301 (probe receipt RowReceipt table)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralGeneratedDictionaryRun299 (Entry run collect)
open CommonRoleOutermostResolver (Dictionary)

theorem receipt_of_entry {s : State roles} {i n : Nat} {entry : Entry}
    (row : rawRow s i = some (site n i).observed)
    (read : (arguments s.core.erased.current.context (focus n i)).bind
      (probe s.core.erased.current.context) = some entry) :
    receipt s i = match entry.children with
      | child :: _ => if attached s i child then .attached entry else .awaitingChild child
      | [] => .attached entry := by
  unfold receipt
  rw [row]
  exact congrArg (fun x : Option Entry => match x with
    | none => RowReceipt.unresolved
    | some found => match found.children with
      | child :: _ => if attached s i child then RowReceipt.attached found else RowReceipt.awaitingChild child
      | [] => RowReceipt.attached found) read

theorem receipt_of_no_entry {s : State roles} {i n : Nat} (row : rawRow s i = some (site n i).observed)
    (read : (arguments s.core.erased.current.context (focus n i)).bind
      (probe s.core.erased.current.context) = none) :
    receipt s i = .unresolved := by
  unfold receipt
  rw [row]
  exact congrArg (fun x : Option Entry => match x with
    | none => RowReceipt.unresolved
    | some found => match found.children with
      | child :: _ => if attached s i child then RowReceipt.attached found else RowReceipt.awaitingChild child
      | [] => RowReceipt.attached found) read

theorem nominal_probe_before (p : Phase n k) (i : Nat) (hi : i ≤ n) :
    (arguments p.state.core.erased.current.context (focus n i)).bind
      (probe p.state.core.erased.current.context) = some ⟨1,[i+1]⟩ := by
  rw [p.context_eq]
  have located : arguments (env p) (focus n i) = some [point n i (by omega)] :=
    GeneralObservedLadderSelection301.located n i _ (by omega)
  rw [located]
  change probe (env p) [_] = _
  unfold probe
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    display_report n i hi,list_as_int n i hi]
  change (if i+1 = i+1 then some (⟨1,[i+1]⟩ : Entry) else none) = _
  simp

theorem scalar_probe_before (p : Phase n k) :
    (arguments p.state.core.erased.current.context (focus n (n+1))).bind
      (probe p.state.core.erased.current.context) = none := by
  rw [p.context_eq]
  have located : arguments (env p) (focus n (n+1)) = some [point n (n+1) (Nat.le_refl _)] :=
    GeneralObservedLadderSelection301.located n (n+1) _ (Nat.le_refl _)
  rw [located]
  change probe (env p) [_] = _
  unfold probe
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralObservedLadderSemanticGap301.old_int_report,GeneralObservedLadderSemanticGap301.old_list_report]
  rfl

theorem raw_row (p : Phase n k) (i : Nat) :
    rawRow p.state i = if i ≤ k then some (site n i).observed else none :=
  GeneralObservedLadderJournalRows301.raw_hit (promotedPhase p) i

theorem attached_edge (p : Phase n k) (i j : Nat) :
    attached p.state i j = true ↔ i < k ∧ j = i+1 :=
  GeneralObservedLadderJournalRows301.attached_exact (promotedPhase p) i j

theorem nominal_receipt (p : Phase n k) (i : Nat) (hi : i ≤ n) (atPhase : i ≤ k) :
    receipt p.state i = if i < k then .attached ⟨1,[i+1]⟩ else .awaitingChild (i+1) := by
  have row : rawRow p.state i = some (site n i).observed := (raw_row p i).trans (ite_eq_left atPhase)
  rw [receipt_of_entry row (nominal_probe_before p i hi)]
  change (if attached p.state i (i+1) = true then RowReceipt.attached ⟨1,[i+1]⟩ else .awaitingChild (i+1)) = _
  simp only [attached_edge p i (i+1),and_true]

theorem scalar_receipt (p : Phase n (n+1)) : receipt p.state (n+1) = .unresolved :=
  receipt_of_no_entry ((raw_row p _).trans (ite_eq_left (Nat.le_refl _))) (scalar_probe_before p)

theorem unavailable (p : Phase n k) (cap : k ≤ n+1) (fuel i : Nat) :
    run (table p.state) fuel i = none := by
  induction fuel generalizing i with
  | zero => rfl
  | succ fuel ih =>
    rw [run]
    unfold table
    by_cases there : i ≤ k
    · by_cases inner : i ≤ n
      · rw [nominal_receipt p i inner there]
        by_cases recorded : i < k
        · rw [ite_eq_left recorded]
          change (do
            let result ← collect (run (table p.state) fuel) [i+1]
            return Dictionary.node 1 result) = none
          rw [collect]
          simp [ih]
        · rw [ite_eq_right recorded]
          rfl
      · have endI : i = n+1 := by omega
        have endK : k = n+1 := by omega
        subst i
        subst k
        rw [scalar_receipt]
        rfl
    · have none : receipt p.state i = .absent := by
        unfold receipt
        rw [raw_row p i,ite_eq_right there]
      rw [none]
      rfl

theorem certified_promotion_table (p : Phase n (n+1)) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (known : GeneralNominalState.Known ctx.state (n+1)) :
    table (refresh p.state ctx) = GeneralObservedLadderObserver301.table n := by
  funext i
  unfold table
  by_cases inner : i ≤ n
  · have row : rawRow (refresh p.state ctx) i = some (site n i).observed :=
      (promoted_raw_row p ctx i).trans (ite_eq_left (by omega))
    rw [receipt_of_entry row (probe_list_after p ctx cert i inner)]
    have edge := (promoted_attachment p ctx i (i+1)).mpr ⟨by omega,rfl⟩
    simpa [edge] using (GeneralObservedLadderObserver301.branch n i inner).symm
  · by_cases last : i = n+1
    · subst i
      have row : rawRow (refresh p.state ctx) (n+1) = some (site n (n+1)).observed :=
        (promoted_raw_row p ctx _).trans (ite_eq_left (Nat.le_refl _))
      rw [receipt_of_entry row (probe_scalar_after p ctx cert known)]
      exact (GeneralObservedLadderObserver301.leaf n).symm
    · have oob : receipt (refresh p.state ctx) i = .absent := by
        unfold receipt
        rw [promoted_raw_row p ctx i,ite_eq_right (by omega)]
      rw [oob]
      exact (GeneralObservedLadderObserver301.out_of_range n i (by omega)).symm

theorem delayed_compile (p : Phase n (n+1)) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    (fuel : Nat) : run (table (refresh p.state ctx)) fuel 0 =
      if n+1 < fuel then some (GeneralObservedLadderEvidence301.dictionary (n+1)) else none := by
  rw [certified_promotion_table p ctx cert known]
  have got := GeneralObservedLadderReadback301.fuel_exact n (n+1) (Nat.le_refl _) fuel
  rwa [Nat.sub_self] at got

end Yulang.GeneralDeferredLadderCompiler302
