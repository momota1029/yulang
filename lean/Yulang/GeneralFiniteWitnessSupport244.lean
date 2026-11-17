import Std
namespace Yulang.GeneralFiniteWitnessSupport244
variable {Name Value : Type}
abbrev Assignment (Name Value : Type) := Name → Value

def Agree (names : List Name) (first last : Assignment Name Value) : Prop :=
 ∀ name ∈ names, first name = last name

def Supports (names : List Name) (predicate : Assignment Name Value → Prop) : Prop :=
 ∀ first last, Agree names first last → (predicate first ↔ predicate last)

def SupportedAt (predicate : Assignment Name Value → Prop) (model : Assignment Name Value) : Prop :=
 ∃ names : List Name, ∀ next, Agree names next model → predicate next

theorem agree_symm (same : Agree names first last) : Agree names last first :=
 fun name member => (same name member).symm

theorem agree_trans (one : Agree names first middle) (two : Agree names middle last) : Agree names first last :=
 fun name member => (one name member).trans (two name member)

theorem agree_append : Agree (left ++ right) first last ↔ Agree left first last ∧ Agree right first last := by
 simp only [Agree,List.mem_append]
 constructor
 · intro h; exact ⟨fun n m => h n (Or.inl m),fun n m => h n (Or.inr m)⟩
 · rintro ⟨h,k⟩ n (m|m); exact h n m; exact k n m

theorem supports_and (one : Supports left P) (two : Supports right Q) :
 Supports (left ++ right) (fun model => P model ∧ Q model) := by
 intro first last same
 have pair := agree_append.mp same
 exact and_congr (one first last pair.1) (two first last pair.2)

theorem supportedAt_and (one : SupportedAt P model) (two : SupportedAt Q model) :
 SupportedAt (fun next => P next ∧ Q next) model := by
 obtain ⟨left,h⟩ := one; obtain ⟨right,k⟩ := two
 exact ⟨left ++ right,fun next same => ⟨h next (agree_append.mp same).1,k next (agree_append.mp same).2⟩⟩

theorem supportedAt_list (items : List α) (predicate : α → Assignment Name Value → Prop)
 (model : Assignment Name Value) (given : ∀ item ∈ items, SupportedAt (predicate item) model) :
 SupportedAt (fun next => ∀ item ∈ items, predicate item next) model := by
 induction items with
 | nil => exact ⟨[],by simp⟩
 | cons first rest ih =>
   obtain ⟨names,h⟩ := supportedAt_and (given first (by simp))
     (ih (fun item member => given item (List.mem_cons_of_mem _ member)))
   exact ⟨names,fun next same item member => by
     rcases List.mem_cons.mp member with rfl | member
     · exact (h next same).1
     · exact (h next same).2 item member⟩

theorem supportedAt_of_supports (support : Supports names predicate) (valid : predicate model) :
 SupportedAt predicate model :=
 ⟨names,fun next same => (support next model same).mpr valid⟩

theorem supportedAt_exists (predicate : α → Assignment Name Value → Prop) (witness : α) (given : SupportedAt (predicate witness) model) :
 SupportedAt (fun next => ∃ x, predicate x next) model := by
 obtain ⟨names,kept⟩ := given
 exact ⟨names,fun next same => ⟨witness,kept next same⟩⟩

def NoRead (writes reads : List Name) : Prop := ∀ name ∈ writes, name ∉ reads

def Preserves (writes : List Name) (first last : Assignment Name Value) : Prop :=
 ∀ name, name ∉ writes → first name = last name

theorem checked_agree (checked : NoRead writes reads) (kept : Preserves writes first last) : Agree reads first last := by
 intro name read
 apply kept name
 intro written
 exact checked name written read

theorem checked_preserves (support : Supports reads predicate) (checked : NoRead writes reads)
 (kept : Preserves writes first last) : predicate first ↔ predicate last :=
 support first last (checked_agree checked kept)

def check [DecidableEq Name] (writes reads : List Name) : Bool :=
 writes.all (fun name => !reads.contains name)

theorem check_iff [DecidableEq Name] (writes reads : List Name) : check writes reads = true ↔ NoRead writes reads := by
 simp [check,NoRead]
end Yulang.GeneralFiniteWitnessSupport244
