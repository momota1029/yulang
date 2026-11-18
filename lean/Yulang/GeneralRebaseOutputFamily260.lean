import Yulang.GeneralRebaseOwnedOutputKeys260
namespace Yulang.GeneralRebaseOutputFamily260
open GeneralRebaseStep258
open GeneralNominalCenteredHeadMatSchemas
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseOwnedOutputKeys260 (key keys)

abbrev Layout := Nat → Schema

def basis (owners : List Nat) (layout : Layout) : List Fact := owners.flatMap fun owner => keys owner (layout owner)

def Holds (owners : List Nat) (layout : Layout)
 (variables : Nat → GeneralNominalMaterialization.Mode → Nat → CommonNominalFullCarrier.Ty)
 (assignment : Assignment) (fact : Fact) : Prop :=
 ∃ owner ∈ owners, GeneralRebaseOwnedOutputKeys260.Holds owner (layout owner) (variables owner) assignment fact

theorem member (owners : List Nat) (layout : Layout) (fact : Fact) :
 fact ∈ basis owners layout ↔ ∃ owner ∈ owners, fact ∈ keys owner (layout owner) := by
 simp only [basis,List.mem_flatMap]

/-- Other owners cannot supply the meaning of this owner's equation address. -/
theorem owner_exact (owners : List Nat) (layout : Layout) (variables) (assignment : Assignment)
 (owner : Nat) (included : owner ∈ owners) (index : Fin (layout owner).equations.length) :
 Holds owners layout variables assignment (key owner index.val) ↔
 (layout owner).equations[index.val].Holds (variables owner) assignment := by
 constructor
 · rintro ⟨other,_,found,same,valid⟩
   obtain ⟨ownerSame,indexSame⟩ := GeneralRebaseOwnedOutputKeys260.key_identity same
   subst other
   have indices : index = found := Fin.ext indexSame
   subst found
   exact valid
 · intro valid
   exact ⟨owner,included,(GeneralRebaseOwnedOutputKeys260.at_index ..).mpr valid⟩

theorem all_exact (owners : List Nat) (layout : Layout) (variables) (assignment : Assignment) :
 (∀ fact ∈ basis owners layout, Holds owners layout variables assignment fact) ↔
 ∀ owner ∈ owners, (layout owner).Holds (variables owner) assignment := by
 constructor
 · intro valid owner included equation present
   obtain ⟨index,bound,equal⟩ := List.mem_iff_getElem.mp present
   have inside : key owner index ∈ basis owners layout :=
     (member ..).mpr ⟨owner,included,(GeneralRebaseOwnedOutputKeys260.member ..).mpr ⟨⟨index,bound⟩,rfl⟩⟩
   have equationValid := (owner_exact owners layout variables assignment owner included ⟨index,bound⟩).mp
     (valid _ inside)
   rwa [equal] at equationValid
 · intro valid fact present
   obtain ⟨owner,included,keyMember⟩ := (member ..).mp present
   exact ⟨owner,included,(GeneralRebaseOwnedOutputKeys260.all_exact ..).mpr (valid owner included) fact keyMember⟩

theorem proposal_closed (owners : List Nat) (layout : Layout) (owner : Nat) (included : owner ∈ owners) :
 keys owner (layout owner) ⊆ basis owners layout :=
 fun _ present => (member ..).mpr ⟨owner,included,present⟩

theorem length (owners : List Nat) (layout : Layout) :
 (basis owners layout).length = (owners.map fun owner => (layout owner).equations.length).sum := by
 induction owners with
 | nil => rfl
 | cons owner rest ih =>
   simp only [basis,List.flatMap_cons,List.length_append,GeneralRebaseOwnedOutputKeys260.length] at *
   simpa using congrArg (Nat.add (layout owner).equations.length) ih
end Yulang.GeneralRebaseOutputFamily260
