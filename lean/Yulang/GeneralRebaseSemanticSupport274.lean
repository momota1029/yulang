import Yulang.GeneralRebaseTerminalRepair274

namespace Yulang.GeneralRebaseSemanticSupport274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedJournalFrame236 (sources models_iff)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty)

def Agreement (pool : List Nat) (first last : Assignment) : Prop :=
 ∀ id ∈ pool, Equivalent (first id).1 (last id).1 ∧ (first id).2 = (last id).2

def splice (pool : List Nat) (first last : Assignment) : Assignment :=
 fun id => if id ∈ pool then last id else first id

theorem splice_in (pool : List Nat) (first last : Assignment) (id : Nat) (inside : id ∈ pool) :
 splice pool first last id = last id := by simp [splice,inside]

theorem splice_out (pool : List Nat) (first last : Assignment) (id : Nat) (outside : id ∉ pool) :
 splice pool first last id = first id := by simp [splice,outside]

theorem splice_equivalent (pool : List Nat) (first last : Assignment) (same : Agreement pool first last) :
 GeneralNominalAssignmentCongruence238.Same first (splice pool first last) := by
 intro id
 by_cases used : id ∈ pool
 · rw [splice_in pool first last id used]
   exact same id used
 · rw [splice_out pool first last id used]
   exact ⟨⟨subtype_refl _,subtype_refl _⟩,rfl⟩

/-- The concrete finite journal read support needs semantic type agreement,
not syntactic equality; there is no hypothesis about irrelevant identities. -/
theorem exact (s : State roles) (legacy : LegacyEmpty s) (first last : Assignment)
 (agree : Agreement (sources s) first last) : Models s first ↔ Models s last :=
 (GeneralNominalVersionedSourceCongruence238.models_iff
   (splice_equivalent (sources s) first last agree) s legacy).trans
 (models_iff s (fun id inside => splice_in (sources s) first last id inside))

theorem extend_support (s : State roles) (legacy : LegacyEmpty s) (pool : List Nat)
 (covered : sources s ⊆ pool) (first last : Assignment)
 (agree : Agreement pool first last) : Models s first ↔ Models s last :=
 exact s legacy first last (fun id read => agree id (covered read))

end Yulang.GeneralRebaseSemanticSupport274
