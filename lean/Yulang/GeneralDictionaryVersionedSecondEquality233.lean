import Yulang.GeneralDictionaryVersionedSecondRaw233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedSecondEquality233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedSecondRaw233
open GeneralDictionaryVersionedSecondInstall233 (installed installed_model)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralDictionaryOptionalCycles229 (Form)
open CommonNominalFullCarrier

inductive Index where
 | zero | one | two | three | four | oldLower | oldUpper | newLower | newUpper

def Index.identity : Index → Nat
 | .zero => 0 | .one => 1 | .two => 2 | .three => 3 | .four => 4
 | .oldLower => oldLo | .oldUpper => oldHi | .newLower => newLo | .newUpper => newHi

def Index.form : Index → Form
 | .zero | .one => .foo
 | .two | .oldUpper | .newLower | .newUpper => .width
 | .three => .top
 | .four | .oldLower => .exact

def canonical : Form → Nat
 | .foo => 0 | .width => 2 | .top => 3 | .exact => 4

theorem index_model (index : Index) : (extended index.identity).1 = index.form.value := by
  cases index
  · exact congrArg Prod.fst (GeneralDictionaryVersionedBothModel233.old_value 0 (by simp [GeneralDictionaryVersionedBothModel233.pool,GeneralDictionaryVersionedInitialModel233.pool]))
  · exact congrArg Prod.fst (GeneralDictionaryVersionedBothModel233.old_value 1 (by simp [GeneralDictionaryVersionedBothModel233.pool,GeneralDictionaryVersionedInitialModel233.pool]))
  · exact congrArg Prod.fst (GeneralDictionaryVersionedBothModel233.old_value 2 (by simp [GeneralDictionaryVersionedBothModel233.pool,GeneralDictionaryVersionedInitialModel233.pool]))
  · exact congrArg Prod.fst (GeneralDictionaryVersionedBothModel233.old_value 3 (by simp [GeneralDictionaryVersionedBothModel233.pool,GeneralDictionaryVersionedInitialModel233.pool]))
  · exact congrArg Prod.fst (GeneralDictionaryVersionedBothModel233.old_value 4 (by simp [GeneralDictionaryVersionedBothModel233.pool,GeneralDictionaryVersionedInitialModel233.pool]))
  · exact GeneralDictionaryVersionedBothModel233.fresh_value 0
  · exact GeneralDictionaryVersionedBothModel233.fresh_value 1
  · exact GeneralDictionaryVersionedBothModel233.next_value 0
  · exact GeneralDictionaryVersionedBothModel233.next_value 1

theorem supported (member : identity ∈ GeneralNominalState.sources installed.core.erased.current.context.state) :
    ∃ index : Index, index.identity = identity := by
  have within := source_support member
  simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.zero,rfl⟩
  · exact ⟨.one,rfl⟩
  · exact ⟨.two,rfl⟩
  · exact ⟨.three,rfl⟩
  · exact ⟨.four,rfl⟩
  · exact ⟨.oldLower,rfl⟩
  · exact ⟨.oldUpper,rfl⟩
  · exact ⟨.newLower,rfl⟩
  · exact ⟨.newUpper,rfl⟩

theorem raw_canonical (index : Index) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models installed.core.erased.current.context.state model) :
    Equivalent (model index.identity).1 (model (canonical index.form)).1 := by
  cases index
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · have equal := alias_zero model (parts valid).1
    exact ⟨equal.2,equal.1⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact ⟨subtype_refl _,subtype_refl _⟩
  · exact (raw_old valid).1
  · exact (raw_old valid).2
  · exact (raw_new valid).1
  · exact (raw_new valid).2

theorem equality_closed : GeneralNominalVersionedTerminalStable233.EqualityClosed installed := by
  intro first last one two equal
  obtain ⟨a,rfl⟩ := supported one
  obtain ⟨b,rfl⟩ := supported two
  have same := equal extended installed_model
  rw [index_model,index_model] at same
  have forms := GeneralDictionaryUpper230Equality.form_injective a.form b.form same
  intro model valid
  have left := raw_canonical a model valid
  have right := raw_canonical b model valid
  rw [forms] at left
  exact ⟨subtype_trans left.1 right.2,subtype_trans right.1 left.2⟩

end Yulang.GeneralDictionaryVersionedSecondEquality233
