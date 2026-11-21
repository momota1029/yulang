import Yulang.GeneralWhereOriginSupport318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 23000000
namespace Yulang.GeneralWhereOriginBatch318
open GeneralDeclarations (Clause)
open GeneralWhereOriginTrace318 (Trace rawOf)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginConfig318 (already_holds)
open GeneralWhereOriginSupport318 (journalSources journal_models)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalVersionedExpressionFrame236 (reads value_eq variableSource variable_value)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralFiniteTypedWrites312 (Coherent Protected Write applyWrites reflexive)
open GeneralVersionedEndpointBatch315 (Proposal compatible outside)
open GeneralDictionaryBinderLocations (sourceSlot)

def proposal (c : Cell p) : Proposal p :=
  ⟨c.side,c.clause,c.index,c.row,c.written.2.origin⟩

def CellOperands (c : Cell p) : List Nat :=
  (reads c.row.mode c.row.expression).map (fun x => variableSource p x.1 x.2)

/-- Solve an actual list of materialized cells that has already been
partitioned into existing recorded lookup and provably fresh writes.
An extra cut can protect any current head/class/source obligations.
This is a common-model theorem, not allocator feasibility or an
operational step. -/
theorem common {j : Journal rs} (checked : (boundary rs).Checked r) (trace : Trace r j)
    (frame : Frame (Compiled r) j.mixed.core focus key p)
    (reuse fresh : List (Cell p)) (guard : List Nat)
    (preserved : ∀ c ∈ reuse, ∃ i, sourceSlot (rawOf j).base c.row.target = some i)
    (absent : ∀ c ∈ fresh, c.row.target ∉ GeneralNominalState.sources (rawOf j) ∧
      c.row.target ∉ journalSources j ∧ c.row.target ∉ guard)
    (notRead : ∀ c ∈ fresh, ∀ other ∈ fresh, c.row.target ∉ CellOperands other)
    (m : Assignment) (valid : Models j m) :
    ∃ n, Models j n ∧ Agree (journalSources j ++ guard) m n ∧
      (∀ c ∈ reuse ++ fresh, c.row.Holds (variables p n) n) := by
  let writes : List Write := fresh.map (fun c => (proposal c).write m)
  let next := applyWrites writes [] m
  have agree (id : Nat) (distinct : ∀ c ∈ fresh, c.row.target ≠ id) : m id = next id := by
    apply outside
    intro w belongs
    obtain ⟨c,present,rfl⟩ := List.mem_map.mp belongs
    exact distinct c present
  have protect : Agree (journalSources j ++ guard) m next := by
    intro id supported
    apply agree
    intro c belongs collide
    rcases List.mem_append.mp supported with earlier|extra
    · exact (absent c belongs).2.1 (collide.symm ▸ earlier)
    · exact (absent c belongs).2.2 (collide.symm ▸ extra)
  have sameModel : Models j next :=
    (journal_models j (fun n h => protect n (List.mem_append_left _ h))).mp valid
  have coherent : Coherent writes := by
    intro a ha b hb eq
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
    change CommonNominalFullCarrier.Equivalent ((proposal x).rhs m) ((proposal y).rhs m)
    rw [compatible _ _ eq m]
    exact reflexive _
  have noProtected : Protected writes [] m := by intro _ _ none; cases none
  have written := GeneralFiniteTypedWrites312.solves writes [] m coherent noProtected
  refine ⟨next,sameModel,protect,?_⟩
  intro c present
  rcases List.mem_append.mp present with prior|new
  · obtain ⟨i,slot⟩ := preserved c prior
    exact already_holds checked trace frame c slot next sameModel
  · have solved := written ((proposal c).write m) (List.mem_map.mpr ⟨c,new,rfl⟩)
    have rhs : value (variables p m) c.row.mode c.row.expression =
        value (variables p next) c.row.mode c.row.expression := by
      apply value_eq
      intro x used
      simp only [variable_value]
      apply congrArg Prod.fst
      apply agree
      exact fun d seen h => notRead d seen c new (h.symm ▸ List.mem_map.mpr ⟨x,used,rfl⟩)
    change CommonNominalFullCarrier.Equivalent (next c.row.target).1
      (value (variables p m) c.row.mode c.row.expression) at solved
    unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
    rw [← rhs]
    exact solved

end Yulang.GeneralWhereOriginBatch318
