import Yulang.GeneralDeclarativeWitnessTypedReemit354
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedReemitPayload354
open GeneralDeclarativeWitnessTypedReemit354 (Linked)
open GeneralDeclarativeWitnessTypedPacket354 (At typedAt)
open GeneralDeclarativeWitnessCompiler350 (portNames)
open GeneralDeclarativeWitnessTypedOutput354 (Write)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCommonBridge (Assignment)

structure Carry {i s w} (a : Linked i s w) (ordinal : Nat) where
  indexed : At (GeneralDeclarativeWitnessTypedChild354.downstream i a.writer.output.state a.child a.out.atWrite.typed.row)
    a.receiver.compiled.readFrom.ctx
    (portNames a.receiver.compiled.readFrom.ctx a.receiver.compiled.ports).input a.child.outputs ordinal
  literal : w.receiver.trace[ordinal]? = some (.typed indexed.typed.row)
  exactSlot : indexed.typed.row.valueName = a.out.atWrite.typed.row.valueName

/-- This checks one actual output occurrence, without authorizing its later release. -/
def check {i s w} (a : Linked i s w) (ordinal : Nat) : Option (Carry a ordinal) := do
  let got ← typedAt a.receiver.compiled.output ordinal
  if actual : got.1.typed.row.valueName = a.out.atWrite.typed.row.valueName then
    some ⟨got.1,a.receiver.exact.symm ▸ got.2,actual⟩
  else none

theorem exact_same_model {i s w} {a : Linked i s w} {ordinal}
    (c : Carry a ordinal) (m : Assignment) (fit : Models s m) :
    a.child.outputs[ordinal]? = some c.indexed.demand ∧
    w.receiver.trace[ordinal]? = some (.typed c.indexed.typed.row) ∧
    c.indexed.typed.row.root = c.indexed.demand.target ∧
    CommonNominalFullCarrier.Equivalent (m c.indexed.typed.row.valueName).1
      (.union (m a.writer.output.source.anchor.first.valueName).1
              (m a.writer.output.source.anchor.last.valueName).1) := by
  refine ⟨c.indexed.indexed,c.literal,rfl,?_⟩
  rw [c.exactSlot]
  exact GeneralDeclarativeWitnessTypedRelease354.actual_payload a.out m fit

theorem fresh_fixed_name_not_prematurely_published {i s w} {a : Linked i s w} {ordinal}
    (c : Carry a ordinal) (m : Assignment)
    (fresh : c.indexed.demand.target ∉
      (GeneralDeclarativeWitnessTypedChild354.downstream i a.writer.output.state a.child a.out.atWrite.typed.row).rows.map
        GeneralDeclarativeWitnessCovariantOrigin353.Row.root) :
    GeneralDeclarativeWitnessTypedReemit354.typedView a m c.indexed.demand.target = none := by
  unfold GeneralDeclarativeWitnessTypedReemit354.typedView GeneralDeclarativeWitnessCovariantCanonical353.valuation
  have nothing :
      (GeneralDeclarativeWitnessTypedChild354.downstream i a.writer.output.state a.child a.out.atWrite.typed.row).rows.find?
        (fun row => row.root == c.indexed.demand.target) = none := by
    apply List.find?_eq_none.mpr
    intro row found
    intro seen
    exact fresh (List.mem_map.mpr ⟨row,found,(beq_iff_eq.mp seen)⟩)
  rw [nothing]
  rfl

end Yulang.GeneralDeclarativeWitnessTypedReemitPayload354
