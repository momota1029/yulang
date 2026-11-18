import Yulang.GeneralRebaseOwnerTags263
import Yulang.GeneralRebaseFactSemantics259

namespace Yulang.GeneralRebaseOwnerTable263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralSourceState (Output)
open GeneralNominalCommonBridge (Assignment)

/-- Finite union of owner tables. Owners and representative Plans are explicit
inputs, not a compiler extracted from source. Duplicate owners are allowed. -/
def basis (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output) : List Fact :=
 owners.flatMap fun owner => GeneralRebaseStableClass261.facts (representative owner) owner pool

def Holds (owners : List Nat) (representative : Nat → Plan roles) (assignment : Assignment) (fact : Fact) : Prop :=
 ∀ owner ∈ owners, GeneralRebaseStableClass261.Holds (representative owner) owner assignment fact

def Models (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 {pool : List Output} (state : State (basis owners representative pool)) (assignment : Assignment) : Prop :=
 GeneralRebaseFactSemantics259.Models base (Holds owners representative) state assignment

theorem member_basis (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (owner : Nat) (listed : owner ∈ owners) (fact : Fact)
 (member : fact ∈ GeneralRebaseStableClass261.facts (representative owner) owner pool) :
 fact ∈ basis owners representative pool := List.mem_flatMap.mpr ⟨owner,listed,member⟩

theorem basis_member (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output) (fact : Fact) :
 fact ∈ basis owners representative pool ↔
 ∃ owner ∈ owners, fact ∈ GeneralRebaseStableClass261.facts (representative owner) owner pool := List.mem_flatMap

theorem proposal_covered (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (owner : Nat) (listed : owner ∈ owners) (outputs : List Output)
 (covered : ∀ output ∈ outputs, output ∈ pool) :
 GeneralRebaseStableClass261.facts (representative owner) owner outputs ⊆ basis owners representative pool := by
 intro fact member
 exact member_basis owners representative pool owner listed fact
   (GeneralRebaseStableClass261.monotone (representative owner) owner outputs pool covered fact member)

theorem holds_owned (owners : List Nat) (representative : Nat → Plan roles)
 (owner : Nat) (listed : owner ∈ owners) (assignment : Assignment) (fact : Fact)
 (tagged : GeneralRebaseOwnerTags263.Tagged owner fact) :
 Holds owners representative assignment fact ↔ GeneralRebaseStableClass261.Holds (representative owner) owner assignment fact :=
 GeneralRebaseOwnerTags263.combined_holds owners representative owner listed assignment fact tagged

/-- On one owner's proposal, conjoining every owner interpretation adds no
foreign-owner restriction. This preserves both directions of the effect equation. -/
theorem all_exact (owners : List Nat) (representative : Nat → Plan roles)
 (owner : Nat) (listed : owner ∈ owners) (outputs : List Output) (assignment : Assignment) :
 (∀ fact ∈ GeneralRebaseStableClass261.facts (representative owner) owner outputs,
   Holds owners representative assignment fact) ↔
 GeneralRebaseClassTable261.Effects (representative owner) outputs assignment := by
 rw [← GeneralRebaseStableClass261.all_exact (representative owner) owner outputs assignment]
 constructor
 · intro valid fact member
   exact (holds_owned owners representative owner listed assignment fact
     (GeneralRebaseOwnerTags263.tagged _ _ _ _ member)).mp (valid fact member)
 · intro valid fact member
   exact (holds_owned owners representative owner listed assignment fact
     (GeneralRebaseOwnerTags263.tagged _ _ _ _ member)).mpr (valid fact member)

/-- Exact global meaning of one owner's write. Other owners' already-written
facts stay in the prior Models conjunct; no source simulation is claimed. -/
theorem write_exact (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (owner : Nat) (listed : owner ∈ owners) (outputs : List Output)
 (covered : ∀ output ∈ outputs, output ∈ pool)
 (state : State (basis owners representative pool)) (assignment : Assignment) :
 Models base owners representative (write state (GeneralRebaseStableClass261.facts (representative owner) owner outputs)) assignment ↔
 Models base owners representative state assignment ∧
 GeneralRebaseClassTable261.Effects (representative owner) outputs assignment := by
 rw [Models,GeneralRebaseFactSemantics259.write_exact]
 apply and_congr Iff.rfl
 constructor
 · intro valid
   apply (all_exact owners representative owner listed outputs assignment).mp
   intro fact member
   exact valid fact (proposal_covered owners representative pool owner listed outputs covered member) member
 · intro valid fact _ member
   exact (all_exact owners representative owner listed outputs assignment).mpr valid fact member

theorem actual_write (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (owner : Nat) (listed : owner ∈ owners)
 (source : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles)
 (covered : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests source root, output ∈ pool)
 (state : State (basis owners representative pool)) (assignment : Assignment) :
 Models base owners representative
   (write state (GeneralRebaseStableClass261.facts (representative owner) owner
     (GeneralNominalCenteredHeadOutputs.requests source root))) assignment ↔
 Models base owners representative state assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects source root (representative owner) assignment :=
 write_exact base owners representative pool owner listed _ covered state assignment

theorem initial_exact (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (assignment : Assignment) :
 Models base owners representative (initial (basis owners representative pool)) assignment ↔ base assignment :=
 GeneralRebaseFactSemantics259.initial_exact ..

theorem done_exact (base : Assignment → Prop) (owners : List Nat) (representative : Nat → Plan roles)
 (pool : List Output) (assignment : Assignment) :
 Models base owners representative (done (basis owners representative pool)) assignment ↔
 base assignment ∧ ∀ owner ∈ owners, GeneralRebaseClassTable261.Effects (representative owner) pool assignment := by
 rw [Models,GeneralRebaseFactSemantics259.done_exact]
 apply and_congr Iff.rfl
 constructor
 · intro valid owner listed
   exact (all_exact owners representative owner listed pool assignment).mp
     (fun fact member => valid fact (member_basis owners representative pool owner listed fact member))
 · intro valid fact member
   obtain ⟨owner,listed,member⟩ := (basis_member owners representative pool fact).mp member
   exact (all_exact owners representative owner listed pool assignment).mpr (valid owner listed) fact member

theorem basis_bound (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output) :
 (basis owners representative pool).length ≤ owners.length * (pool.length + pool.length * pool.length) :=
 GeneralRebaseOwnerTags263.tables_bound owners representative pool

/-- Number of effective finite writes, not observer work or source Steps. -/
theorem run_bound (owners : List Nat) (representative : Nat → Plan roles) (pool : List Output)
 (observe : Observer (basis owners representative pool)) {steps before after}
 (run : GeneralRebaseBudget258.Runs observe steps before after) :
 steps ≤ owners.length * (pool.length + pool.length * pool.length) := by
 have budget := GeneralRebaseBudget258.budget observe run
 have finite := before.canonical.length_le
 have limit := basis_bound owners representative pool
 omega
end Yulang.GeneralRebaseOwnerTable263
