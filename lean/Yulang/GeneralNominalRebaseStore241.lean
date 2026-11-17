import Yulang.GeneralNominalCommonBridge
set_option backward.isDefEq.respectTransparency false
/-! Owner-indexed replacement, distinct from append-only historical conjunction.
Public atoms are retained. No source-projection or boundary claim follows from
this representation alone. -/
namespace Yulang.GeneralNominalRebaseStore241
open PresenceNormalForm GeneralNominalCommonBridge
abbrev Block := List (Atom Nat)
abbrev Owner := Nat × Nat
abbrev Store := Owner → Block
variable {assignment : Assignment}

def replace (store : Store) (owner : Owner) (block : Block) : Store :=
 fun key => if key = owner then block else store key

theorem replace_at : replace store owner block owner = block := by simp [replace]
theorem replace_other (different : key ≠ owner) :
 replace store owner block key = store key := by simp [replace,different]
theorem replace_overwrite : replace (replace store owner first) owner last = replace store owner last := by
 funext key; by_cases same : key = owner <;> simp [replace,same]
theorem replace_current : replace store owner (store owner) = store := by
 funext key; by_cases same : key = owner <;> simp [replace,same]
theorem replace_commute (different : first ≠ last) :
 replace (replace store first firstBlock) last lastBlock =
 replace (replace store last lastBlock) first firstBlock := by
 funext key
 by_cases one : key = first
 · subst key; simp [replace,different]
 · by_cases two : key = last
   · subst key; simp [replace,one]
   · simp [replace,one,two]

def Models (baseAtoms : Block) (owners : List Owner) (store : Store) (assignment : Assignment) : Prop :=
 All CommonNominalFullCarrier.model assignment baseAtoms ∧
 ∀ owner ∈ owners, All CommonNominalFullCarrier.model assignment (store owner)

theorem models_replace_iff (present : owner ∈ owners) :
 Models baseAtoms owners (replace store owner block) assignment ↔
 All CommonNominalFullCarrier.model assignment baseAtoms ∧
 All CommonNominalFullCarrier.model assignment block ∧
 ∀ other ∈ owners, other ≠ owner → All CommonNominalFullCarrier.model assignment (store other) := by
 constructor
 · intro valid
   refine ⟨valid.1,?_,?_⟩
   · simpa only [replace_at] using valid.2 owner present
   · intro other member different
     simpa only [replace_other different] using valid.2 other member
 · rintro ⟨base,current,rest⟩
   refine ⟨base,?_⟩
   intro other member
   by_cases same : other = owner
   · subst other; simpa only [replace_at] using current
   · simpa only [replace_other same] using rest other member same

theorem public_retained (valid : Models baseAtoms owners (replace store owner block) assignment) :
 All CommonNominalFullCarrier.model assignment baseAtoms := valid.1

theorem outside_retained (valid : Models baseAtoms owners (replace store owner block) assignment)
 (present : other ∈ owners) (different : other ≠ owner) :
 All CommonNominalFullCarrier.model assignment (store other) := by
 simpa only [replace_other different] using valid.2 other present

structure State where
 baseAtoms : Block
 owners : List Owner
 blocks : Store

def rebase (state : State) (owner : Owner) (block : Block) : State :=
 {state with blocks := replace state.blocks owner block}

theorem rebase_public : (rebase state owner block).baseAtoms = state.baseAtoms := rfl
theorem rebase_owners : (rebase state owner block).owners = state.owners := rfl
theorem rebase_count : (rebase state owner block).owners.length = state.owners.length := rfl
end Yulang.GeneralNominalRebaseStore241
