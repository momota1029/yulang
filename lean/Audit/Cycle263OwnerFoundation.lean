import Yulang.GeneralRebaseOwnerTags263
import Yulang.GeneralRebaseOwnerTable263
#print axioms Yulang.GeneralRebaseOwnerTags263.Tagged
#print axioms Yulang.GeneralRebaseOwnerTags263.body_tagged
#print axioms Yulang.GeneralRebaseOwnerTags263.tagged
#print axioms Yulang.GeneralRebaseOwnerTags263.owner_unique
#print axioms Yulang.GeneralRebaseOwnerTags263.tables_separate
#print axioms Yulang.GeneralRebaseOwnerTags263.foreign_holds
#print axioms Yulang.GeneralRebaseOwnerTags263.tables_bound
#print axioms Yulang.GeneralRebaseOwnerTags263.combined_holds
#print axioms Yulang.GeneralRebaseOwnerTable263.basis
#print axioms Yulang.GeneralRebaseOwnerTable263.Holds
#print axioms Yulang.GeneralRebaseOwnerTable263.Models
#print axioms Yulang.GeneralRebaseOwnerTable263.member_basis
#print axioms Yulang.GeneralRebaseOwnerTable263.basis_member
#print axioms Yulang.GeneralRebaseOwnerTable263.proposal_covered
#print axioms Yulang.GeneralRebaseOwnerTable263.holds_owned
#print axioms Yulang.GeneralRebaseOwnerTable263.all_exact
#print axioms Yulang.GeneralRebaseOwnerTable263.write_exact
#print axioms Yulang.GeneralRebaseOwnerTable263.actual_write
#print axioms Yulang.GeneralRebaseOwnerTable263.initial_exact
#print axioms Yulang.GeneralRebaseOwnerTable263.done_exact
#print axioms Yulang.GeneralRebaseOwnerTable263.basis_bound
#print axioms Yulang.GeneralRebaseOwnerTable263.run_bound
#check @Yulang.GeneralRebaseOwnerTable263.actual_write
#check @Yulang.GeneralRebaseOwnerTable263.run_bound

open Yulang GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

example (first last : Plan roles) (outputs : List Output) (fact : Fact) :
 ¬ (fact ∈ GeneralRebaseStableClass261.facts first 38 outputs ∧
    fact ∈ GeneralRebaseStableClass261.facts last 39 outputs) :=
 GeneralRebaseOwnerTags263.tables_separate first last 38 39 (by decide) outputs outputs fact

/-- One real global Models predicate retains both owners' writes. -/
example (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (one two : Nat) (listedOne : one ∈ owners) (listedTwo : two ∈ owners)
 (first last : List Output) (firstCovered : first ⊆ pool) (lastCovered : last ⊆ pool)
 (state : State (GeneralRebaseOwnerTable263.basis owners representative pool)) (assignment : Assignment) :
 GeneralRebaseOwnerTable263.Models base owners representative
   (write (write state (GeneralRebaseStableClass261.facts (representative one) one first))
     (GeneralRebaseStableClass261.facts (representative two) two last)) assignment ↔
 GeneralRebaseOwnerTable263.Models base owners representative state assignment ∧
 GeneralRebaseClassTable261.Effects (representative one) first assignment ∧
 GeneralRebaseClassTable261.Effects (representative two) last assignment := by
 rw [GeneralRebaseOwnerTable263.write_exact base owners representative pool two listedTwo last lastCovered,
   GeneralRebaseOwnerTable263.write_exact base owners representative pool one listedOne first firstCovered]
 exact and_assoc

example (representative : Nat → Plan roles) (pool : List Output) :
 (GeneralRebaseOwnerTable263.basis [] representative pool).length = 0 := rfl
example (representative : Nat → Plan roles) (pool : List Output) :
 (GeneralRebaseOwnerTable263.basis [4,4] representative pool).length ≤ 2 * (pool.length + pool.length * pool.length) :=
 GeneralRebaseOwnerTable263.basis_bound [4,4] representative pool
