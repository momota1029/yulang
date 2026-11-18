import Yulang.GeneralOutputRebasePublic260
namespace Yulang.GeneralRebaseOwnedOutputKeys260
open GeneralRebaseStep258
open GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCommonBridge (Assignment)

def key (owner index : Nat) : Fact := .binder (2 + GeneralNominalIdentities.pair owner index)
def keys (owner : Nat) (schema : Schema) : List Fact :=
 (List.range schema.equations.length).map (key owner)

/-- A finite equation-table address, not a newly allocated source name. -/
def Holds (owner : Nat) (schema : Schema) (variables : GeneralNominalMaterialization.Mode → Nat → CommonNominalFullCarrier.Ty) (assignment : Assignment) (fact : Fact) : Prop :=
 ∃ index : Fin schema.equations.length,
 fact = key owner index.val ∧ schema.equations[index.val].Holds variables assignment

theorem key_identity {firstOwner firstIndex lastOwner lastIndex : Nat}
 (same : key firstOwner firstIndex = key lastOwner lastIndex) :
 firstOwner = lastOwner ∧ firstIndex = lastIndex := by
 have encoded := Fact.binder.inj same
 have paired : GeneralNominalIdentities.pair firstOwner firstIndex = GeneralNominalIdentities.pair lastOwner lastIndex :=
   Nat.add_left_cancel encoded
 have samePair : (firstOwner,firstIndex) = (lastOwner,lastIndex) := GeneralNominalIdentities.pair_injective paired
 exact ⟨congrArg Prod.fst samePair,congrArg Prod.snd samePair⟩

theorem key_injective (owner : Nat) {first last : Nat} (same : key owner first = key owner last) : first = last :=
 (key_identity same).2

theorem member (owner : Nat) (schema : Schema) (fact : Fact) :
 fact ∈ keys owner schema ↔ ∃ index : Fin schema.equations.length, fact = key owner index.val := by
 simp only [keys,List.mem_map,List.mem_range]
 constructor
 · rintro ⟨index,bound,equal⟩; exact ⟨⟨index,bound⟩,equal.symm⟩
 · rintro ⟨index,equal⟩; exact ⟨index.val,index.isLt,equal.symm⟩

theorem at_index (owner : Nat) (schema : Schema) (variables) (assignment : Assignment)
 (index : Fin schema.equations.length) :
 Holds owner schema variables assignment (key owner index.val) ↔
 schema.equations[index.val].Holds variables assignment := by
 constructor
 · rintro ⟨other,same,valid⟩
   have indices : index = other := Fin.ext (key_injective owner same)
   subst other
   exact valid
 · intro valid; exact ⟨index,rfl,valid⟩

/-- All actual emitted equations, with no semantic premise supplied by a caller. -/
theorem all_exact (owner : Nat) (schema : Schema) (variables) (assignment : Assignment) :
 (∀ fact ∈ keys owner schema, Holds owner schema variables assignment fact) ↔
 schema.Holds variables assignment := by
 constructor
 · intro valid equation present
   obtain ⟨index,bound,equal⟩ := List.mem_iff_getElem.mp present
   have value :=  (at_index owner schema variables assignment ⟨index,bound⟩).mp
     (valid (key owner index) ((member ..).mpr ⟨⟨index,bound⟩,rfl⟩))
   rwa [equal] at value
 · intro valid fact present
   obtain ⟨index,rfl⟩ := (member ..).mp present
   exact (at_index owner schema variables assignment index).mpr
     (valid _ (List.getElem_mem index.isLt))

theorem capture_separate (owner : Nat) (schema : Schema) (index : Nat) (below : index < 2) :
 .binder index ∉ keys owner schema := by
 intro present
 obtain ⟨found,equal⟩ := (member ..).mp present
 have same := Fact.binder.inj equal
 omega

theorem owners_separate (first last : Nat) (different : first ≠ last)
 (firstSchema lastSchema : Schema) (fact : Fact) :
 ¬ (fact ∈ keys first firstSchema ∧ fact ∈ keys last lastSchema) := by
 rintro ⟨one,two⟩
 obtain ⟨left,leftKey⟩ := (member ..).mp one
 obtain ⟨right,rightKey⟩ := (member ..).mp two
 exact different (key_identity (leftKey.symm.trans rightKey)).1

theorem length (owner : Nat) (schema : Schema) : (keys owner schema).length = schema.equations.length := by
 simp [keys]
end Yulang.GeneralRebaseOwnedOutputKeys260
