import YulangClosure.SimpleSubRegularCompletion
import YulangClosure.SimpleSubRegularDecision

/-!
Join constructive completion, evolving graphs, concrete constraint steps and
computed terminal evidence. Graph allocation may be interleaved with actual
constraint operations; earlier steps are lifted into the final graph by proved
prefix preservation. Original obligations are interpreted in that one final
graph and one shared reference assignment.

This removes the fixed-graph-history, supplied-decoding and supplied-certificate
requirements of the preceding structural bridge. It does not derive native
success, row realization, inventory coverage or original source Call evidence.
Union/intersection and native open-row/coalescing semantics remain separate.
-/
namespace YulangClosure.SimpleSub.GrowingInference
open Regular RegularPublication RegularExtension RegularCompletion RegularDecision

/-- A finite trace alternates exact structural steps and literal graph growth.
Constructors contain no semantic preservation or satisfying-model premise. -/
inductive GrowingHistory (ref : Nat → Nat → Prop) (birth : Nat → Nat) :
    Graph → ConstraintState → Graph → ConstraintState → Prop where
  | nil (graph : Graph) (state : ConstraintState) : GrowingHistory ref birth graph state graph state
  | step {graph before middle target after}
      (change : ConstraintStep graph ref birth before middle)
      (rest : GrowingHistory ref birth graph middle target after) :
      GrowingHistory ref birth graph before target after
  | grow {graph next state target after}
      (extension : Extends graph next)
      (rest : GrowingHistory ref birth next state target after) :
      GrowingHistory ref birth graph state target after

theorem GrowingHistory.extension {ref birth graph first target last}
    (history : GrowingHistory ref birth graph first target last) : Extends graph target := by
  induction history with
  | nil graph state => exact Extends.refl graph
  | step change rest ih => exact ih
  | grow extension rest ih => exact extension.trans ih

theorem GrowingHistory.flatten {ref birth graph first target last}
    (history : GrowingHistory ref birth graph first target last) :
    ConstraintHistory target ref birth first last := by
  induction history with
  | nil graph state => exact .nil state
  | step change rest ih => exact .cons (rest.extension.step change) ih
  | grow extension rest ih => exact ih

theorem GrowingHistory.append {ref birth graph first middle midState target last}
    (left : GrowingHistory ref birth graph first middle midState)
    (right : GrowingHistory ref birth middle midState target last) :
    GrowingHistory ref birth graph first target last := by
  induction left with
  | nil => exact right
  | step change rest ih => exact .step change (ih right)
  | grow extension rest ih => exact .grow extension (ih right)

theorem GrowingHistory.of_fixed {ref birth graph first last}
    (history : ConstraintHistory graph ref birth first last) :
    GrowingHistory ref birth graph first graph last := by
  induction history with
  | nil state => exact .nil graph state
  | cons change rest ih => exact .step change ih

theorem GrowingHistory.decided_sound {ref birth graph first target last}
    (history : GrowingHistory ref birth graph first target last)
    (decided : decideDemands target last.obligations = true) :
    Extends graph target ∧ target.Valid ∧ Holds target first.obligations :=
  ⟨history.extension, decided_original_demands history.flatten decided⟩

/-- The original store is decoded by construction and its interpretation
survives all subsequent allocations and transformations in the final graph. -/
theorem completed_growing_store_sound {graph refs store}
    (valid : graph.Valid) (lawful : LawfulStore graph refs store) :
    let result := completedStore graph refs store
    ∀ {events ref birth target last},
      GrowingHistory ref birth result.1 ⟨result.2,events⟩ target last →
      decideDemands target last.obligations = true →
      Extends graph target ∧ target.Valid ∧ StoreSatisfied target refs store := by
  intro result events ref birth target last history decided
  have completed := completedStore_correct valid lawful
  have decoded := history.extension.decode_store completed.2.2
  exact ⟨completed.1.trans history.extension,
    decided_store_history decoded history.flatten decided⟩

/-- Main connection: missing constructor nodes and terminal evidence are both
computed. Local graph growth, history and all clients retain one final graph. -/
theorem completed_growing_publication_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store}
    (valid : graph.Valid)
    (lawful : LawfulStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))))
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory) :
    let result := completedStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q)))
    ∀ {events ref birth target last},
      GrowingHistory ref birth result.1 ⟨result.2,events⟩ target last →
      decideDemands target last.obligations = true →
      Extends graph target ∧ target.Valid ∧
        PublishedSatisfied target (fun k i => refs k (publicationTransport n count afterUse q k i))
          n bounds beforeCap beforeUse roots uses ∧
        StoreSatisfied target (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  intro result events ref birth target last history decided
  have completed := completedStore_correct valid lawful
  refine ⟨completed.1.trans history.extension, ?_⟩
  exact decided_publication_with_clients bounded images closed stops useBounds coverage
    (history.extension.decode_store completed.2.2) history.flatten decided

/-! Interleaved allocation: decompose an existing cyclic Function, allocate a
new tuple, insert and discharge a constraint on that fresh node, then compute
terminal evidence. No final pair table is supplied. -/
def grownCycles : Graph := appendNode twoCycles (.tuple [0,1])

def cycleChildren : ConstraintState :=
  ⟨[⟨.value,1,0⟩,⟨.effect,0,0⟩,⟨.effect,0,0⟩,⟨.value,0,1⟩],[]⟩

theorem interleaved_history : GrowingHistory (fun _ _ => False) (fun _ => 0)
    twoCycles cyclicInitial grownCycles cycleChildren := by
  apply GrowingHistory.step
    (ConstraintStep.decompose ⟨.value,0,1⟩ cycleChildren.obligations [] [] rfl)
  apply GrowingHistory.grow (appendNode_extends twoCycles (.tuple [0,1]))
  apply GrowingHistory.step (ConstraintStep.insertLower .value 2 2 cycleChildren)
  apply GrowingHistory.step
    (ConstraintStep.reflexive .value 2 cycleChildren.obligations [] ⟨.tuple [0,1],rfl⟩)
  exact .nil _ _

theorem interleaved_decided : decideDemands grownCycles cycleChildren.obligations = true := by decide

theorem interleaved_original_solved :
    Extends twoCycles grownCycles ∧ grownCycles.Valid ∧ Holds grownCycles cyclicInitial.obligations :=
  interleaved_history.decided_sound interleaved_decided

end YulangClosure.SimpleSub.GrowingInference
