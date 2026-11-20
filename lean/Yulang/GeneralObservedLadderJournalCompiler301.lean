import Yulang.GeneralObservedLadderJournalRows301

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderJournalCompiler301
open GeneralObservedLadderReport301 (point display_report int_report int_as_list list_as_int)
open GeneralObservedLadderPlan301 (occurrence)
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralObservedLadderJournalRows301
open GeneralObservedLadderObserver301 (finish reject)
open GeneralObservedLadderEvidence301 (final dictionary)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (intDisplay displayRoot registry)
open GeneralNominalRecursiveCandidates (arguments report Context)
open GeneralNominalRecursiveInspection (bindings)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralGeneratedDictionaryRun299 (Read Entry run collect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open CommonRoleOutermostResolver (Dictionary)

inductive RowReceipt where
  | absent
  | unresolved
  | awaitingChild (child : Nat)
  | attached (entry : Entry)
  deriving DecidableEq

def probe (c : Context) (bs : List (GeneralNominalInspection.Bounds c.state)) : Option Entry :=
  let lists := report c display bs
  let scalars := report c intDisplay bs
  if finish lists && reject scalars then
    match bindings c.state lists with
    | [(0,(lo,hi))] => if lo = hi then some ⟨display.id,[lo]⟩ else none
    | _ => none
  else if reject lists && finish scalars then some ⟨intDisplay.id,[]⟩
  else none

/-- Read actual recorded rows, recompute head reports in the current context,
and check the recorded edge before making a recursive row available. -/
def receipt (s : State roles) (i : Nat) : RowReceipt :=
  match rawRow s i with
  | none => .absent
  | some row =>
    let ctx := s.core.erased.current.context
    match (arguments ctx row.occurrence).bind (probe ctx) with
    | none => RowReceipt.unresolved
    | some e =>
      match e.children with
      | child :: _ => if attached s i child then RowReceipt.attached e else RowReceipt.awaitingChild child
      | [] => RowReceipt.attached e

def table (s : State roles) : Read := fun i =>
  match receipt s i with
  | .attached e => some e
  | _ => none

theorem probe_list (p : Phase n k) (i : Nat) (hi : i ≤ n) :
    probe (env p) [point n i (by omega)] = some ⟨1,[i+1]⟩ := by
  unfold probe
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    display_report n i hi,list_as_int n i hi]
  change (if i+1 = i+1 then some (⟨1,[i+1]⟩ : Entry) else none) = _
  simp

theorem probe_leaf (p : Phase n k) :
    probe (env p) [point n (n+1) (Nat.le_refl _)] = some ⟨3,[]⟩ := by
  unfold probe
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.candidate_report_extended,int_as_list,int_report]
  rfl

theorem checked_list (p : Phase n k) (i : Nat) (recorded : i ≤ k) (inner : i ≤ n) :
    receipt p.state i = if i < k then .attached ⟨1,[i+1]⟩ else .awaitingChild (i+1) := by
  unfold receipt
  rw [raw_hit p i,ite_eq_left recorded]
  have seen : (arguments p.state.core.erased.current.context (focus n i)).bind
      (probe p.state.core.erased.current.context) = some ⟨1,[i+1]⟩ := by
    rw [p.context_eq]
    have locate : arguments (env p) (focus n i) = some [point n i (by omega)] :=
      GeneralObservedLadderSelection301.located n i (invocation n i) (by omega)
    rw [locate]
    exact probe_list p i inner
  change (match (arguments p.state.core.erased.current.context (focus n i)).bind
      (probe p.state.core.erased.current.context) with
      | none => RowReceipt.unresolved
      | some e => match e.children with
        | child :: _ => if attached p.state i child then RowReceipt.attached e else RowReceipt.awaitingChild child
        | [] => RowReceipt.attached e) = _
  rw [seen]
  change (if attached p.state i (i+1) = true then RowReceipt.attached ⟨1,[i+1]⟩ else .awaitingChild (i+1)) = _
  simp only [attached_exact p i (i+1),and_true]

theorem checked_leaf (p : Phase n (n+1)) : receipt p.state (n+1) = .attached ⟨3,[]⟩ := by
  unfold receipt
  rw [raw_hit p (n+1),ite_eq_left (Nat.le_refl _)]
  have seen : (arguments p.state.core.erased.current.context (focus n (n+1))).bind
      (probe p.state.core.erased.current.context) = some ⟨3,[]⟩ := by
    rw [p.context_eq]
    have locate : arguments (env p) (focus n (n+1)) = some [point n (n+1) (Nat.le_refl _)] :=
      GeneralObservedLadderSelection301.located n (n+1) (invocation n (n+1)) (Nat.le_refl _)
    rw [locate]
    exact probe_leaf p
  change (match (arguments p.state.core.erased.current.context (focus n (n+1))).bind
      (probe p.state.core.erased.current.context) with
      | none => RowReceipt.unresolved
      | some e => match e.children with
        | child :: _ => if attached p.state (n+1) child then RowReceipt.attached e else RowReceipt.awaitingChild child
        | [] => RowReceipt.attached e) = _
  rw [seen]

theorem unrecorded (p : Phase n k) (i : Nat) (missing : k < i) : receipt p.state i = .absent := by
  unfold receipt
  rw [raw_hit p i,ite_eq_right (by omega)]

theorem exact_final (n : Nat) : table (final n).state = GeneralObservedLadderObserver301.table n := by
  funext i
  unfold table
  by_cases hi : i ≤ n
  · rw [checked_list (final n) i (by omega) hi,ite_eq_left (by omega),
      GeneralObservedLadderObserver301.branch n i hi]
  by_cases atEnd : i = n+1
  · subst i
    rw [checked_leaf,GeneralObservedLadderObserver301.leaf]
  rw [unrecorded (final n) i (by omega),GeneralObservedLadderObserver301.out_of_range n i (by omega)]

theorem before_no_dictionary (p : Phase n k) (before : k ≤ n) (gas i : Nat) :
    run (table p.state) gas i = none := by
  induction gas generalizing i with
  | zero => rfl
  | succ gas ih =>
    rw [run]
    unfold table
    by_cases there : i ≤ k
    · rw [checked_list p i there (by omega)]
      by_cases old : i < k
      · rw [ite_eq_left old]
        change (do
          let gathered ← collect (run (table p.state) gas) [i+1]
          return Dictionary.node 1 gathered) = none
        rw [collect]
        simp [ih]
      · rw [ite_eq_right old]
        rfl
    · rw [unrecorded p i (by omega)]
      rfl

theorem root_available_exact (n k : Nat) (cap : k ≤ n+1) (gas : Nat) :
    run (table (GeneralObservedLadderAdvance301.run n k cap).state) gas 0 =
      if k = n+1 ∧ n+1 < gas then some (dictionary (n+1)) else none := by
  by_cases ready : k = n+1
  · subst k
    change run (table (final n).state) gas 0 = _
    rw [exact_final]
    have exact := GeneralObservedLadderReadback301.fuel_exact n (n+1) (Nat.le_refl _) gas
    rw [Nat.sub_self] at exact
    simpa using exact
  have before : k ≤ n := by omega
  rw [before_no_dictionary (GeneralObservedLadderAdvance301.run n k cap) before gas 0]
  simp [ready]

theorem semantic_at_final (n i gas : Nat) (d : Dictionary)
    (pass : run (table (final n).state) gas i = some d) (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models (final n).state m) :
    (boundary roles).Evidence registry (final n).state m (focus n i) d := by
  rw [exact_final] at pass
  exact GeneralObservedLadderReadback301.compiler_sound n i gas d pass m valid

end Yulang.GeneralObservedLadderJournalCompiler301
