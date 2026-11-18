import Yulang.GeneralRebaseStableClass261

namespace Yulang.GeneralRebaseQuadraticBudget262
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)

theorem flatMap_bound (values : List α) (emit : α → List β) (limit : Nat)
 (bounded : ∀ value ∈ values, (emit value).length ≤ limit) :
 (values.flatMap emit).length ≤ values.length * limit := by
 induction values with
 | nil => simp
 | cons first rest ih =>
   simp only [List.flatMap_cons,List.length_append,List.length_cons]
   have one := bounded first List.mem_cons_self
   have tail := ih (fun value member => bounded value (List.mem_cons_of_mem _ member))
   have both := Nat.add_le_add one tail
   simpa [Nat.add_mul,Nat.one_mul,Nat.add_comm] using both

theorem schema_bound (plan : Plan roles) (output : Output) :
 (GeneralRebaseBodyTable261.schema plan output).equations.length ≤ 1 := by
 unfold GeneralRebaseBodyTable261.schema
 cases GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name with
 | none => simp
 | some body =>
   dsimp only
   unfold GeneralNominalCenteredHeadMatEffects.bodySchema
   split <;> simp

theorem keys_bound (plan : Plan roles) (owner : Nat) (output : Output) :
 (GeneralRebaseBodyTable261.keys plan owner output).length ≤ 1 := by
 simpa only [GeneralRebaseBodyTable261.keys,GeneralRebaseOwnedOutputKeys260.keys,
   List.length_map,List.length_range] using schema_bound plan output

theorem bodies_bound (plan : Plan roles) (owner : Nat) (outputs : List Output) :
 (GeneralRebaseBodyTable261.facts plan owner outputs).length ≤ outputs.length := by
 simpa only [Nat.mul_one,GeneralRebaseBodyTable261.facts] using flatMap_bound outputs (GeneralRebaseBodyTable261.keys plan owner) 1
   (fun output _ => keys_bound plan owner output)

theorem pairs_bound (owner : Nat) (outputs : List Output) :
 (GeneralRebasePairKeys261.facts owner outputs).length ≤ outputs.length * outputs.length := by
 apply flatMap_bound
 intro output _
 simp only [List.length_map]
 exact List.length_filter_le ..

/-- Counts the actual emitted body and same-name pair facts, including list
multiplicity. No deduplication or semantic readiness assumption is required. -/
theorem facts_bound (plan : Plan roles) (owner : Nat) (outputs : List Output) :
 (GeneralRebaseStableClass261.facts plan owner outputs).length ≤ outputs.length + outputs.length * outputs.length := by
 simpa only [GeneralRebaseStableClass261.facts,List.length_append] using
   Nat.add_le_add (bodies_bound plan owner outputs) (pairs_bound owner outputs)

/-- This bounds nontrivial rebase writes, not source-language transitions,
observer running time, graph-search work or full compiler complexity. -/
theorem run_bound (plan : Plan roles) (owner : Nat) (pool : List Output)
 (observe : Observer (GeneralRebaseStableClass261.facts plan owner pool))
 {n before after} (run : GeneralRebaseBudget258.Runs observe n before after) :
 n ≤ pool.length + pool.length * pool.length := by
 have budget := GeneralRebaseBudget258.budget observe run
 have initial := before.canonical.length_le
 have facts := facts_bound plan owner pool
 omega
end Yulang.GeneralRebaseQuadraticBudget262
