import Yulang.GeneralRebaseCompoundPublic273

set_option maxRecDepth 12000
set_option maxHeartbeats 1800000
namespace Yulang.GeneralRebaseCompoundSourceTypes273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundFrame238 (before)
open GeneralNominalVersionedJournal232 (Models)
open GeneralSourceState (equationAtoms)
open GeneralRebaseCompoundPublic273 (view Fixed)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

def Prefix (boundary : Assignment) : Prop := ∀ id < 4, Equivalent (boundary id).1 (view id)

def PublicSource (boundary : Assignment) : Prop :=
 Prefix boundary ∧ Subtype (boundary 4).1 (boundary 2).1

theorem source_reads (m : Assignment) (source : GeneralNominalState.Models snapshot m) :
 PublicSource m := by
 refine ⟨?_,lower_width m source⟩
 intro id low
 have cases4 : id = 0 ∨ id = 1 ∨ id = 2 ∨ id = 3 := by omega
 rcases cases4 with rfl | rfl | rfl | rfl
 · exact root_fixed m source
 · exact equivalent_trans ⟨(alias_zero m source).2,(alias_zero m source).1⟩ (root_fixed m source)
 · exact width_two m source
 · exact top_three m source

theorem source_write (m : Assignment) (wanted : PublicSource m) : GeneralNominalState.Models snapshot m := by
 have zero : Equivalent (m 0).1 foo := wanted.1 0 (by decide)
 have one : Equivalent (m 1).1 foo := wanted.1 1 (by decide)
 have two : Equivalent (m 2).1 .emptyRecord := wanted.1 2 (by decide)
 have three : Equivalent (m 3).1 .top := wanted.1 3 (by decide)
 refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro atom member
   simp only [base,equationAtoms,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with (((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | rfl
   · exact subtype_trans zero.1 one.2
   · exact subtype_trans one.1 zero.2
   · exact two.1
   · exact two.2
   · exact three.1
   · exact three.2
   · exact wanted.2
 · intro slot term recorded
   by_cases isTwo : slot = 2
   · subst slot
     cases Option.some.inj recorded
     exact two
   · simp [base,isTwo,GeneralSourceState.Head.equation] at recorded
 · intro bounds member; cases member
 · intro slot descriptorAt recorded
   by_cases z : slot = 0
   · subst slot
     cases Option.some.inj recorded
     refine ⟨[.inl .emptyRecord,.inl .emptyRecord],.cons ?_ (.cons ?_ .nil),zero⟩
     all_goals exact ⟨subtype_trans wanted.2 two.1,two.2⟩
   · by_cases o : slot = 1
     · subst slot
       cases Option.some.inj recorded
       refine ⟨[.inl .emptyRecord,.inl .emptyRecord],.cons ?_ (.cons ?_ .nil),one⟩
       all_goals exact ⟨two.1,two.2⟩
     · simp [z,o] at recorded

theorem before_exact (m : Assignment) : Models before m ↔ PublicSource m := by
 rw [GeneralNominalVersionedJournal232.initial_models context root m]
 exact ⟨fun h => source_reads _ h.1,fun source =>
   ⟨source_write _ source,GeneralNominalCenters.point_root_holds _ _ root_point _⟩⟩

def Body (m : Assignment) : Prop := Equivalent (m 4).1 GeneralDictionaryOptionalOutput229.value

theorem restricted_exact (m : Assignment) : Fixed m ↔ PublicSource m ∧ Body m := by
 constructor
 · intro full
   have four : Body m := full 4 (by decide)
   have two : Equivalent (m 2).1 .emptyRecord := full 2 (by decide)
   exact ⟨⟨fun id small => full id (by omega),
     subtype_trans four.1 (subtype_trans GeneralDictionaryOptionalOutput229.below_width two.2)⟩,four⟩
 · rintro ⟨source,body⟩ id bounded
   by_cases small : id < 4
   · exact source.1 id small
   · have same : id = 4 := by omega
     cases same
     exact body

theorem source_depends_on_types (first last : Assignment)
 (same : GeneralRebaseCompoundPublic273.AgreesTypes first last) : PublicSource first ↔ PublicSource last := by
 unfold PublicSource Prefix
 have lt4 : ∀ id < 4, (first id).1 = (last id).1 := fun id small => same id (by omega)
 refine and_congr ?_ (by rw [same 4 (by decide),same 2 (by decide)])
 exact forall_congr' fun i => forall_congr' fun h => by rw [lt4 i h]

end Yulang.GeneralRebaseCompoundSourceTypes273
