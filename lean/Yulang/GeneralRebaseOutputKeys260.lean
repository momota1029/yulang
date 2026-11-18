import Yulang.GeneralRebaseBatchOrder259
namespace Yulang.GeneralRebaseOutputKeys260
open GeneralRebaseStep258
open GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCommonBridge (Assignment)

def key (offset index : Nat) : Fact := .binder (offset+index)
def keys (offset : Nat) (schema : Schema) : List Fact :=
 (List.range schema.equations.length).map (key offset)

/-- A finite equation-table address, not a newly allocated source name. -/
def Holds (offset : Nat) (schema : Schema) (variables : GeneralNominalMaterialization.Mode → Nat → CommonNominalFullCarrier.Ty) (assignment : Assignment) (fact : Fact) : Prop :=
 ∃ index : Fin schema.equations.length,
 fact = key offset index.val ∧ schema.equations[index.val].Holds variables assignment

theorem key_injective (offset : Nat) {first last : Nat} (same : key offset first = key offset last) : first = last := by
 have equal := Fact.binder.inj same
 omega

theorem member (offset : Nat) (schema : Schema) (fact : Fact) :
 fact ∈ keys offset schema ↔ ∃ index : Fin schema.equations.length, fact = key offset index.val := by
 simp only [keys,List.mem_map,List.mem_range]
 constructor
 · rintro ⟨index,bound,equal⟩; exact ⟨⟨index,bound⟩,equal.symm⟩
 · rintro ⟨index,equal⟩; exact ⟨index.val,index.isLt,equal.symm⟩

theorem at_index (offset : Nat) (schema : Schema) (variables) (assignment : Assignment)
 (index : Fin schema.equations.length) :
 Holds offset schema variables assignment (key offset index.val) ↔
 schema.equations[index.val].Holds variables assignment := by
 constructor
 · rintro ⟨other,same,valid⟩
   have indices : index = other := Fin.ext (key_injective offset same)
   subst other
   exact valid
 · intro valid; exact ⟨index,rfl,valid⟩

/-- All actual emitted equations, with no semantic premise supplied by a caller. -/
theorem all_exact (offset : Nat) (schema : Schema) (variables) (assignment : Assignment) :
 (∀ fact ∈ keys offset schema, Holds offset schema variables assignment fact) ↔
 schema.Holds variables assignment := by
 constructor
 · intro valid equation present
   obtain ⟨index,bound,equal⟩ := List.mem_iff_getElem.mp present
   have value :=  (at_index offset schema variables assignment ⟨index,bound⟩).mp
     (valid (key offset index) ((member ..).mpr ⟨⟨index,bound⟩,rfl⟩))
   rwa [equal] at value
 · intro valid fact present
   obtain ⟨index,rfl⟩ := (member ..).mp present
   exact (at_index offset schema variables assignment index).mpr
     (valid _ (List.getElem_mem index.isLt))

theorem below_offset (offset : Nat) (schema : Schema) (index : Nat) (below : index < offset) :
 .binder index ∉ keys offset schema := by
 intro present
 obtain ⟨found,equal⟩ := (member ..).mp present
 have same := Fact.binder.inj equal
 omega

theorem length (offset : Nat) (schema : Schema) : (keys offset schema).length = schema.equations.length := by
 simp [keys]
end Yulang.GeneralRebaseOutputKeys260
