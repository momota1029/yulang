import Yulang.GeneralWhereOriginCompiler318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralWhereOriginDelta318
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenters (Plan)
open GeneralNominalState (State sources)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralVersionedEndpointAddress315 (Side atCell key)
open GeneralNominalIdentities (Origin source)
open GeneralWhereVersionCompiler317 (schema)
open GeneralWhereVersionStoredRow317 (Endpoint)
open GeneralDictionaryBinderLocations (sourceSlot sourceSlot_exact)

/-- The namespace in which both corrected compiler polarities allocate. -/
def High (st : State) (n : Nat) : Prop :=
  ∃ k : Origin, 9 < k.2.2.1 ∧ n = source st.seed k

structure Cell (p : Plan rs) where
  clause : Clause
  index : Nat
  side : Side
  pattern : Pattern
  expression : Expr
  listed : clause ∈ p.packet.declaration.requirements
  located : clause.arguments[index]? = some pattern
  compound : ∀ n, normalize pattern ≠ .var n
  translated : translate p.packet.registry.constructors p.packet.context.interpretation pattern = some expression

def Cell.row (c : Cell p) : Equation :=
  ⟨atCell p c.side c.clause.id c.index c.expression,c.side.mode,c.expression⟩

theorem Cell.written (c : Cell p) :
    c.row ∈ (schema p).equations ∧ Endpoint p c.side c.clause c.index c.row :=
  GeneralWhereOriginCompiler318.materialized c.listed c.located c.compound c.translated c.side

theorem Cell.high (c : Cell p) (same : t.seed = p.packet.context.state.seed) : High t c.row.target := by
  refine ⟨key p c.side c.clause.id c.index c.expression,?_,?_⟩
  · change 9 < c.side.purpose
    cases c.side <;> decide
  · simp only [Cell.row,atCell,same]

/-- Layout check for an actual compiler transaction. Every new high
raw source position is paired with one previously absent write
from a checked source cell. Old raw coordinates are preserved.
This is a new producer contract, not a property of arbitrary legacy
refresh or fabricated context refinements. -/
structure Delta (before after : State) (p : Plan rs) where
  refinement : GeneralNominalRefinements.Refines before after
  current : p.packet.context.state = before
  cells : List (Cell p)
  absent : ∀ c ∈ cells, c.row.target ∉ sources before
  fresh_slot : ∀ c ∈ cells, ∃ i, after.base.source i = c.row.target
  split_slot : ∀ i : Fin after.base.slots, High after (after.base.source i) →
    (∃ j : Fin before.base.slots, after.base.source i = before.base.source j) ∨
      ∃ c ∈ cells, after.base.source i = c.row.target

structure Keeps (before after : State) where
  refinement : GeneralNominalRefinements.Refines before after
  no_insert : ∀ i : Fin after.base.slots, High after (after.base.source i) →
    ∃ j : Fin before.base.slots, after.base.source i = before.base.source j

theorem prior_lookup (refines : GeneralNominalRefinements.Refines before after)
    (old : sourceSlot before.base n = some i) :
    sourceSlot after.base n = some (refines.base.embed i) :=
  (sourceSlot_exact ..).mpr ((refines.base.source i).trans ((sourceSlot_exact ..).mp old))

end Yulang.GeneralWhereOriginDelta318
