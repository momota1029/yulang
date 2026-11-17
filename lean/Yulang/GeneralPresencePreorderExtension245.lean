import Yulang.GeneralPresenceModelExtension245
import Yulang.GeneralPresenceAbsorb245
import Yulang.GeneralPresenceModelCongruence245
/-! Projected model equivalence for a congruent subtype preorder, without
antisymmetry or equality of equivalent private type representations.
The nominal Common model law producer is supplied in GeneralPresenceCommonLaws245. -/
namespace Yulang.GeneralPresencePreorderExtension245
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceOwnerOwnership244 GeneralPresenceReadback245
open GeneralPresenceModelCongruence245
open GeneralPresenceModelExtension245 (readback_absorbs)
variable {Name Owner : Type} [DecidableEq Name]

theorem readback_compatible (entries : List (Entry Name)) (model : Model)
 (laws : Laws model) (assignment : Name → Comp model)
 (valid : All model assignment (block entries)) :
 Compatible model (readback entries model assignment) assignment := by
 intro name
 refine ⟨?_,rfl⟩
 cases found : lookup entries name with
 | none =>
   simp only [readback,substitution,found,Option.getD_none,CompTerm.eval,TyTerm.eval]
   exact ⟨laws.refl _,laws.refl _⟩
 | some term =>
   have member := lookup_member found
   have forward : model.subTy (assignment name).1 (term.eval model assignment) :=
     valid (.tyLe (.var name) term) (List.mem_flatMap.mpr ⟨(name,term),member,by simp [equations]⟩)
   have backward : model.subTy (term.eval model assignment) (assignment name).1 :=
     valid (.tyLe term (.var name)) (List.mem_flatMap.mpr ⟨(name,term),member,by simp [equations]⟩)
   simpa [Equiv,readback,substitution,found,CompTerm.eval] using And.intro backward forward

variable [DecidableEq Owner]

theorem models_extension (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (present : owner ∈ state.owners)
 (disjoint : ∀ other ∈ state.owners, other ≠ owner → DisjointTargets (state.entries owner) (state.entries other))
 (oldExternal : External (state.entries owner)) (oldCoherent : Coherent (state.entries owner))
 (freshExternal : External fresh) (freshCoherent : Coherent fresh)
 (within : TargetsWithin fresh (state.entries owner))
 (model : Model) (laws : Laws model)
 (assignment : Name → Comp model) (valid : Models state model assignment) :
 Models (rebase state owner fresh) model (readback fresh model assignment) := by
 apply (models_exact state owner fresh present disjoint model _).mpr
 refine ⟨block_holds fresh freshExternal freshCoherent model laws.refl assignment,?_⟩
 change Consumers state owner model (readback (state.entries owner) model (readback fresh model assignment))
 rw [readback_absorbs _ _ oldExternal oldCoherent within]
 have compatible := readback_compatible _ model laws assignment (valid.2 owner present)
 refine ⟨(all_iff laws compatible state.base).mpr valid.1,?_⟩
 intro other member _
 exact (all_iff laws compatible (block (state.entries other))).mpr (valid.2 other member)

def Agrees (sharedNames : Name → Prop) (model : Model) (first last : Name → Comp model) : Prop :=
 ∀ name, sharedNames name → first name = last name

/-- Equality of projected solution sets, not equality of private assignments. -/
theorem public_models_iff (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (present : owner ∈ state.owners)
 (disjoint : ∀ other ∈ state.owners, other ≠ owner → DisjointTargets (state.entries owner) (state.entries other))
 (oldExternal : External (state.entries owner)) (oldCoherent : Coherent (state.entries owner))
 (freshExternal : External fresh) (freshCoherent : Coherent fresh)
 (within : TargetsWithin fresh (state.entries owner))
 (sharedNames : Name → Prop) (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ state.entries owner, entry.1 ≠ name)
 (model : Model) (laws : Laws model)
 (boundary : Name → Comp model) :
 (∃ assignment, Models state model assignment ∧ Agrees sharedNames model assignment boundary) ↔
 (∃ assignment, Models (rebase state owner fresh) model assignment ∧ Agrees sharedNames model assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨readback fresh model assignment,
     models_extension state owner fresh present disjoint oldExternal oldCoherent freshExternal freshCoherent within model laws assignment valid,?_⟩
   intro name shared
   rw [outside_preserved fresh model assignment name]
   · exact agree name shared
   · intro entry member
     obtain ⟨old,oldMem,equal⟩ := within entry member
     rw [← equal]
     exact privateTargets name shared old oldMem
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨readback (state.entries owner) model assignment,
     models_readback state owner fresh present disjoint oldExternal oldCoherent model laws.refl assignment valid,?_⟩
   intro name shared
   rw [outside_preserved _ model assignment name (privateTargets name shared)]
   exact agree name shared
end Yulang.GeneralPresencePreorderExtension245
