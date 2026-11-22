import Yulang.GeneralDeclarativeWherePlain346
import Yulang.GeneralDeclarativeWhereRawTicket346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWhereBatchReady346
open GeneralNominalCenters (Plan)
open GeneralWhereVersionInstall317 (Journal)
open GeneralWhereOriginDelta318 (Delta Cell)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginInstall318 (RawTicket)
open GeneralNominalVersionedExpressionFrame236 (reads variableSource)
open GeneralDeclarativeWhereRawAtoms346 (cell batch)
open GeneralDeclarativeWherePlain346 (Plain complete)
open GeneralWherePhysicalBase319 (Layout expand)
open GeneralWherePhysicalNominal319 (Extra)
open GeneralWherePhysicalDeferred319 (laid)
open GeneralDeclarativeWhereRawTicket346 (emitted gives_ticket)
open GeneralSourceState (State)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)
open GeneralNominalCandidates (Context)

theorem ready_cell (s : State) {p : Plan rs} (c : Cell p)
    (target : ∃ i, sourceSlot s c.row.target = some i)
    (shape : Plain c.expression)
    (visible : ∀ key ∈ reads c.side.mode c.expression,
      ∃ i, sourceSlot s (variableSource p c.side.mode key.2) = some i) :
    ∃ atoms, cell s c = some atoms := by
  obtain ⟨slot,located⟩ := target
  obtain ⟨term,printed⟩ := complete shape (fun k => sourceSlot s (variableSource p c.side.mode k)) c.side.mode visible
  refine ⟨GeneralSourceState.equationAtoms slot term,?_⟩
  unfold cell
  rw [located,printed]
  rfl

theorem ready_batch (s : State) {p : Plan rs} (xs : List (Cell p))
    (tickets : ∀ c ∈ xs, ∃ atoms, cell s c = some atoms) :
    ∃ atoms, batch s xs = some atoms := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨a,printed⟩ := tickets x List.mem_cons_self
    obtain ⟨b,later⟩ := ih (fun c found => tickets c (List.mem_cons_of_mem _ found))
    refine ⟨a++b,?_⟩
    unfold batch
    rw [printed,later]
    rfl

/-- For an actual checked fresh layout the target lookup follows
from the layout, not a second semantic assumption. Independent
operand lookup and structural representability are still explicit. -/
theorem checked_layout {j : Journal rs} {p : Plan rs} {n : Nat}
    (l : Layout (rawOf j).base n) {ctx : Context} (delta : Delta (rawOf j) ctx.state p)
    (positions : Fin ctx.state.base.slots → Fin (expand l []).slots)
    (same : ∀ i, (expand l []).source (positions i) = ctx.state.base.source i)
    (shapes : ∀ c ∈ delta.cells, Plain c.expression)
    (operands : ∀ c ∈ delta.cells, ∀ key ∈ reads c.side.mode c.expression,
      ∃ i, sourceSlot (expand l []) (variableSource p c.side.mode key.2) = some i) :
    ∃ atoms : Extra (rawOf j) n, emitted l delta.cells = some atoms := by
  change ∃ atoms, batch (expand l []) delta.cells = some atoms
  refine ready_batch (expand l []) delta.cells ?_
  intro c found
  apply ready_cell _ c _ (shapes c found) (operands c found)
  obtain ⟨i,exactName⟩ := delta.fresh_slot c found
  exact ⟨positions i,(sourceSlot_exact ..).mpr ((same i).trans exactName)⟩

end Yulang.GeneralDeclarativeWhereBatchReady346
