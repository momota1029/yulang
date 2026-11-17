import Yulang.GeneralPresenceReadback245
import Yulang.GeneralPresenceAbsorb245
/-! Two-way projected solutions for an explicitly reflexive, antisymmetric
model. The general Model signature supplies neither law. Fresh blocks must be
external and coherent, with targets confined to the replaced private block.
No source-operation producer or solver completeness is asserted. -/
namespace Yulang.GeneralPresenceModelExtension245
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceOwnerOwnership244 GeneralPresenceReadback245
variable {Name Owner : Type} [DecidableEq Name]

theorem readback_fixed (entries : List (Entry Name)) (model : Model)
 (antisymm : ∀ first last, model.subTy first last → model.subTy last first → first = last)
 (assignment : Name → Comp model) (valid : All model assignment (block entries)) :
 readback entries model assignment = assignment := by
 funext name
 apply Prod.ext
 · cases found : lookup entries name with
   | none => simp [readback,substitution,found,CompTerm.eval,TyTerm.eval]
   | some term =>
     have member := lookup_member found
     have forward : model.subTy (assignment name).1 (term.eval model assignment) :=
       valid (.tyLe (.var name) term) (List.mem_flatMap.mpr ⟨(name,term),member,by simp [equations]⟩)
     have backward : model.subTy (term.eval model assignment) (assignment name).1 :=
       valid (.tyLe term (.var name)) (List.mem_flatMap.mpr ⟨(name,term),member,by simp [equations]⟩)
     simpa [readback,substitution,found,CompTerm.eval] using antisymm _ _ backward forward
 · rfl

-- The absorption lemma is stated separately at the actual syntax level.
theorem readback_absorbs (old fresh : List (Entry Name))
 (external : External old) (coherent : Coherent old) (within : TargetsWithin fresh old)
 (model : Model) (assignment : Name → Comp model) :
 readback old model (readback fresh model assignment) = readback old model assignment := by
 funext name
 apply Prod.ext
 · have equal := congrArg (fun term : TyTerm Name => term.eval model assignment)
     (GeneralPresenceAbsorb245.mapping_absorb old fresh external coherent within name)
   rw [TyTerm.eval_subst] at equal
   exact equal
 · rfl

variable [DecidableEq Owner]

theorem models_extension (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (present : owner ∈ state.owners)
 (disjoint : ∀ other ∈ state.owners, other ≠ owner → DisjointTargets (state.entries owner) (state.entries other))
 (oldExternal : External (state.entries owner)) (oldCoherent : Coherent (state.entries owner))
 (freshExternal : External fresh) (freshCoherent : Coherent fresh)
 (within : TargetsWithin fresh (state.entries owner))
 (model : Model) (refl : ∀ value, model.subTy value value)
 (antisymm : ∀ first last, model.subTy first last → model.subTy last first → first = last)
 (assignment : Name → Comp model) (valid : Models state model assignment) :
 Models (rebase state owner fresh) model (readback fresh model assignment) := by
 apply (models_exact state owner fresh present disjoint model _).mpr
 refine ⟨block_holds fresh freshExternal freshCoherent model refl assignment,?_⟩
 change Consumers state owner model (readback (state.entries owner) model (readback fresh model assignment))
 rw [readback_absorbs _ _ oldExternal oldCoherent within,
   readback_fixed _ model antisymm assignment (valid.2 owner present)]
 exact ⟨valid.1,fun other member _ => valid.2 other member⟩

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
 (model : Model) (refl : ∀ value, model.subTy value value)
 (antisymm : ∀ first last, model.subTy first last → model.subTy last first → first = last)
 (boundary : Name → Comp model) :
 (∃ assignment, Models state model assignment ∧ Agrees sharedNames model assignment boundary) ↔
 (∃ assignment, Models (rebase state owner fresh) model assignment ∧ Agrees sharedNames model assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨readback fresh model assignment,
     models_extension state owner fresh present disjoint oldExternal oldCoherent freshExternal freshCoherent within model refl antisymm assignment valid,?_⟩
   intro name shared
   rw [outside_preserved fresh model assignment name]
   · exact agree name shared
   · intro entry member
     obtain ⟨old,oldMem,equal⟩ := within entry member
     rw [← equal]
     exact privateTargets name shared old oldMem
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨readback (state.entries owner) model assignment,
     models_readback state owner fresh present disjoint oldExternal oldCoherent model refl assignment valid,?_⟩
   intro name shared
   rw [outside_preserved _ model assignment name (privateTargets name shared)]
   exact agree name shared
end Yulang.GeneralPresenceModelExtension245
