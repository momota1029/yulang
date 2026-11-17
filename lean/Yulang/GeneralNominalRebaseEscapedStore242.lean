import Yulang.GeneralNominalRebaseEscapedReplace242
import Yulang.GeneralNominalRebaseStore241
set_option backward.isDefEq.respectTransparency false
/-! Whole finite ordinary owner-table replacement. Every base and other-owner
atom is retained by old-definition inlining. Nominal descriptors and non-atom
journal consumers are outside this table's representation. -/
namespace Yulang.GeneralNominalRebaseEscapedStore242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseInline241
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebaseStore241 (Owner Store Block Models)

def definitionBlock (entries : List Entry) : Block :=
 entries.flatMap (fun entry => GeneralNominalAllocation.equations entry.1 entry.2)

noncomputable def inline (entries : List Entry) (atoms : Block) : Block :=
 atoms.map (atomSubst (substitution entries))

def consumers (base : Block) (owners : List Owner) (store : Store) (owner : Owner) : Block :=
 base ++ owners.flatMap (fun key => if key = owner then [] else store key)

noncomputable def replaceAll (store : Store) (owner : Owner)
 (oldEntries newEntries : List Entry) : Store :=
 fun key => if key = owner then definitionBlock newEntries else inline oldEntries (store key)

theorem definitions_iff (entries : List Entry) (model : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model (definitionBlock entries) ↔
 Definitions entries model := by
 constructor
 · intro valid entry member atom present
   exact valid atom (List.mem_flatMap.mpr ⟨entry,member,present⟩)
 · intro valid atom member
   obtain ⟨entry,present,inside⟩ := List.mem_flatMap.mp member
   exact valid entry present atom inside

theorem consumers_iff (base : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (model : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model (consumers base owners store owner) ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model model base ∧
 ∀ key ∈ owners, key ≠ owner → PresenceNormalForm.All CommonNominalFullCarrier.model model (store key) := by
 rw [consumers,PresenceNormalForm.all_append]
 apply and_congr_right
 intro _
 constructor
 · intro valid key member different atom present
   exact valid atom (List.mem_flatMap.mpr ⟨key,member,by simpa only [different,ite_false] using present⟩)
 · intro valid atom member
   obtain ⟨key,present,inside⟩ := List.mem_flatMap.mp member
   by_cases same : key = owner
   · simp only [same,ite_true,List.not_mem_nil] at inside
   · exact valid key present same atom (by simpa only [same,ite_false] using inside)

theorem old_models_iff (base : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (entries : List Entry) (present : owner ∈ owners) (oldBlock : store owner = definitionBlock entries)
 (model : Assignment) : Models base owners store model ↔
 Definitions entries model ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model model (consumers base owners store owner) := by
 rw [consumers_iff]
 constructor
 · intro valid
   refine ⟨(definitions_iff entries model).mp ?_,valid.1,fun key member _ => valid.2 key member⟩
   rw [← oldBlock]
   exact valid.2 owner present
 · rintro ⟨definitions,baseValid,others⟩
   refine ⟨baseValid,?_⟩
   intro key member
   by_cases same : key = owner
   · subst key
     rw [oldBlock]
     exact (definitions_iff entries model).mpr definitions
   · exact others key member same

theorem inline_consumers_iff (base : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (entries : List Entry) (model : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model (inline entries (consumers base owners store owner)) ↔
 PresenceNormalForm.All CommonNominalFullCarrier.model model (inline entries base) ∧
 ∀ key ∈ owners, key ≠ owner → PresenceNormalForm.All CommonNominalFullCarrier.model model (inline entries (store key)) := by
 unfold inline
 simp only [PresenceNormalForm.All,List.forall_mem_map]
 change (∀ atom ∈ consumers base owners store owner,
   (atomSubst (substitution entries) atom).Holds CommonNominalFullCarrier.model model) ↔ _
 constructor
 · intro valid
   constructor
   · intro atom member
     exact valid atom (List.mem_append_left _ member)
   · intro key member different atom inside
     exact valid atom (List.mem_append_right _ (List.mem_flatMap.mpr
       ⟨key,member,by simpa only [different,ite_false] using inside⟩))
 · rintro ⟨baseValid,others⟩ atom member
   rcases List.mem_append.mp member with one | other
   · exact baseValid atom one
   · obtain ⟨key,present,inside⟩ := List.mem_flatMap.mp other
     by_cases same : key = owner
     · simp only [same,ite_true,List.not_mem_nil] at inside
     · exact others key present same atom (by simpa only [same,ite_false] using inside)

theorem new_models_iff (base : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (oldEntries newEntries : List Entry) (present : owner ∈ owners) (model : Assignment) :
 Models (inline oldEntries base) owners (replaceAll store owner oldEntries newEntries) model ↔
 Definitions newEntries model ∧
 PresenceNormalForm.All CommonNominalFullCarrier.model model
   (inline oldEntries (consumers base owners store owner)) := by
 rw [inline_consumers_iff]
 constructor
 · intro valid
   have current := valid.2 owner present
   simp only [replaceAll,ite_true] at current
   refine ⟨(definitions_iff newEntries model).mp current,valid.1,?_⟩
   intro key member different
   have other := valid.2 key member
   simpa only [replaceAll,different,ite_false] using other
 · rintro ⟨definitions,baseValid,others⟩
   refine ⟨baseValid,?_⟩
   intro key member
   by_cases same : key = owner
   · subst key
     simpa only [replaceAll,ite_true] using (definitions_iff newEntries model).mpr definitions
   · simpa only [replaceAll,same,ite_false] using others key member same

theorem projection_iff (base : Block) (owners : List Owner) (store : Store) (owner : Owner)
 (oldEntries newEntries : List Entry) (present : owner ∈ owners)
 (oldBlock : store owner = definitionBlock oldEntries)
 (oldCoherent : Coherent oldEntries) (oldExternal : External oldEntries)
 (newCoherent : Coherent newEntries) (newExternal : External newEntries)
 (within : TargetsWithin newEntries oldEntries) (model : Assignment) :
 (∃ old, Preserves oldEntries old model ∧ Models base owners store old) ↔
 (∃ next, Preserves oldEntries next model ∧
   Models (inline oldEntries base) owners (replaceAll store owner oldEntries newEntries) next) := by
 have ordinary := replacement_projection_iff oldEntries newEntries oldCoherent oldExternal
   newCoherent newExternal within (consumers base owners store owner) model
 constructor
 · rintro ⟨old,kept,valid⟩
   obtain ⟨next,preserved,definitions,atoms⟩ := ordinary.mp
     ⟨old,kept,(old_models_iff base owners store owner oldEntries present oldBlock old).mp valid⟩
   exact ⟨next,preserved,(new_models_iff base owners store owner oldEntries newEntries present next).mpr ⟨definitions,atoms⟩⟩
 · rintro ⟨next,kept,valid⟩
   obtain ⟨old,preserved,definitions,atoms⟩ := ordinary.mpr
     ⟨next,kept,(new_models_iff base owners store owner oldEntries newEntries present next).mp valid⟩
   exact ⟨old,preserved,(old_models_iff base owners store owner oldEntries present oldBlock old).mpr ⟨definitions,atoms⟩⟩
end Yulang.GeneralNominalRebaseEscapedStore242
