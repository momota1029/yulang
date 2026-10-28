import YulangClosure.SourceIdentityWorld

/-!
The original contextual Function membership application stops at a semantic
interpretation, not at the identity's raw Name operation. This module checks
both sides of that distinction against the actual receipt constructor already
represented by SourceIdentityWorld:

* a pending binding receipt can be materialized without changing any observer
  of the complete receiving record;
* an abstraction that instead reflects already executed Receive evidence at
  every administrative state cannot stutter across a first Name read.

The pending receipt is explicit source/native relation data. It is not asserted
to be an executed native receipt, a source typing certificate, an admitted
challenge, a final valid world, or original ValueMem. Its equality theorem is
only the receiving-component square needed by an interpretation. Original
PhiW/P_F, dictionary meaning, declared-hole interpretation and annotation
realization are deliberately not replaced by these definitions.
-/
namespace YulangClosure.SourceFunctionMembership

open NativeClosureEnvironment SourceIdentityWorld

/-- A genuinely recorded receipt, retaining the exact owner, view, source slot
and optional formal. The bound excludes unallocated Store cells. -/
def Recorded (r : Receiving K V ViewData Site) (receipt : Receipt K Site) : Prop :=
  ∃ i, i < r.receipts.size ∧ r.receipts.cell i = some receipt

/-- The owner/view projection used by the original Receive/Path join. This
does not assert activity, protection, a grant, or an executing observation. -/
def ReceivedBy (r : Receiving K V ViewData Site) (owner : Owner) (view : Nat) : Prop :=
  ∃ receipt, Recorded r receipt ∧ receipt.owner = owner ∧ receipt.view = view

theorem recorded_after_read [DecidableEq K]
    (r : Receiving K V ViewData Site) (owner : Owner) (view : Nat) (site : Site)
    (receipt : Receipt K Site) :
    Recorded (r.record owner view site none) receipt ↔
      Recorded r receipt ∨ receipt = ⟨owner, view, site, none⟩ := by
  constructor
  · rintro ⟨i, bound, found⟩
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ bound) with old | fresh
    · exact .inl ⟨i, old, (push_old _ _ _ old).symm.trans found⟩
    · subst i
      exact .inr (Option.some.inj ((push_current _ _).symm.trans found)).symm
  · rintro (⟨i, bound, found⟩ | same)
    · exact ⟨i, Nat.lt_trans bound (Nat.lt_succ_self _),
        (push_old _ _ _ bound).trans found⟩
    · subst receipt
      exact ⟨r.receipts.size, Nat.lt_succ_self _, push_current _ _⟩

theorem receivedBy_after_read [DecidableEq K]
    (r : Receiving K V ViewData Site) (owner : Owner) (view : Nat) (site : Site)
    (candidate : Owner) (candidateView : Nat) :
    ReceivedBy (r.record owner view site none) candidate candidateView ↔
      ReceivedBy r candidate candidateView ∨
        (candidate = owner ∧ candidateView = view) := by
  constructor
  · rintro ⟨receipt, recorded, ownerEq, viewEq⟩
    rcases (recorded_after_read r owner view site receipt).mp recorded with old | fresh
    · exact .inl ⟨receipt, old, ownerEq, viewEq⟩
    · cases fresh
      exact .inr ⟨ownerEq.symm, viewEq.symm⟩
  · rintro (old | same)
    · obtain ⟨receipt, recorded, ownerEq, viewEq⟩ := old
      exact ⟨receipt, (recorded_after_read r owner view site receipt).mpr (.inl recorded),
        ownerEq, viewEq⟩
    · rcases same with ⟨ownerEq, viewEq⟩
      subst candidate
      subst candidateView
      exact ⟨⟨owner, view, site, none⟩,
        (recorded_after_read r owner view site _).mpr (.inr rfl), rfl, rfl⟩

/-- Two implementation phases for one source binding receipt. At `binding`
the native read has not happened. The constructor data comes from the actual
bound value and currently executing owner. At `executed` it has happened. -/
inductive ReceivingPhase (K V ViewData Site : Type) where
  | binding (receiving : Receiving K V ViewData Site)
      (owner : Owner) (view : Nat) (site : Site)
  | executed (receiving : Receiving K V ViewData Site)

/-- Candidate phase-indexed realization of the source binding receipt. The
full record is retained, including receipt identities, the last-receipt index,
all earlier records, all sites/formals, and the unchanged view registry. -/
def ReceivingPhase.realize [DecidableEq K] :
    ReceivingPhase K V ViewData Site → Receiving K V ViewData Site
  | .binding r owner view site => r.record owner view site none
  | .executed r => r

theorem binding_receipt_materialization [DecidableEq K]
    (r : Receiving K V ViewData Site) (owner : Owner) (view : Nat) (site : Site) :
    (ReceivingPhase.binding r owner view site).realize =
      (ReceivingPhase.executed (r.record owner view site none)).realize := rfl

/-- No receipt observer is erased by this phase-indexed materialization:
the two complete receiving records are literally equal after realization. -/
theorem materialization_all_observers [DecidableEq K]
    (r : Receiving K V ViewData Site) (owner : Owner) (view : Nat) (site : Site)
    (observe : Receiving K V ViewData Site → α) :
    observe (ReceivingPhase.binding r owner view site).realize =
      observe (ReceivingPhase.executed (r.record owner view site none)).realize := rfl

/-- Apply the square to the identity's actually constructed parameter binding.
The native Name success is derived from lookup and the actual registered view;
it is not a premise. The actual dispatch result remains explicit. -/
theorem identity_name_materialization [DecidableEq K] [DecidableEq V]
    (w : World K D V ViewData Site Rest) (parent : Nat) (key : K)
    (p : Received V) (node : Node K D)
    (found : nodeAt w.environments parent = some node)
    (site : Site) (dispatch : Option Nat) (matching : Matches w.receiving p) :
    let bound := bindValue w parent key p node found
    let read := { bound with
      receiving := w.receiving.record w.control.current p.view site none }
    observeName bound w.environments.size key site dispatch =
      some (read, p.asValue.atName dispatch) ∧
    (ReceivingPhase.binding bound.receiving bound.control.current p.view site).realize =
      (ReceivingPhase.executed read.receiving).realize := by
  refine ⟨?_, rfl⟩
  simpa only [bindValue, Received.asValue] using
    (name_success (site := site) (dispatch := dispatch)
      (bind_read w parent key p node found) matching)

/-- Exact obstruction to a different bridge: if no receipt exists before
the first read, there cannot be one unchanged abstract state whose Receive
predicate reflects executed native receipts both before and after it.

This names the genuine owner/view Receive premise of Path; it is not a
countermodel formed by inventing an arbitrary rejecting full-envelope guard.
It does not preclude the explicit binding-phase realization above. -/
theorem no_executed_receive_reflecting_stutter [DecidableEq K]
    (r : Receiving K V ViewData Site) (owner : Owner) (view : Nat) (site : Site)
    (firstRead : ¬ ReceivedBy r owner view)
    (Abstract : Type) (relate : Receiving K V ViewData Site → Abstract → Prop)
    (receive : Abstract → Owner → Nat → Prop)
    (reflect : ∀ native abstract, relate native abstract →
      (receive abstract owner view ↔ ReceivedBy native owner view)) :
    ¬ ∃ abstract, relate r abstract ∧ relate (r.record owner view site none) abstract := by
  rintro ⟨abstract, before, after⟩
  have executed : ReceivedBy (r.record owner view site none) owner view :=
    (receivedBy_after_read r owner view site owner view).mpr (.inr ⟨rfl, rfl⟩)
  have observed := (reflect _ _ after).mpr executed
  exact firstRead ((reflect _ _ before).mp observed)

end YulangClosure.SourceFunctionMembership
