import Yulang.GeneralPresenceOrderedSubstitution247
import Yulang.GeneralPresenceOrderedDependence247
import Yulang.GeneralPresenceCommonLaws245
/-! Public solution preservation for actual finite Presence atom substitution
of an acyclic ordered private block, including unguarded aliases/lattice terms.
The source-operation ordering/ownership producer and metadata coverage remain
separate. Cyclic unguarded equations are not asserted covered by SafeOrder. -/
namespace Yulang.GeneralPresenceOrderedRebase247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedSubstitution247
open GeneralPresenceModelCongruence245
variable {Name : Type} [DecidableEq Name]

def Agrees (model : Model) (sharedNames : Name → Prop) (first last : Name → Comp model) : Prop :=
 ∀ name, sharedNames name → first name = last name

theorem models_forward (model : Model) (laws : Laws model) (old fresh : List (Entry Name))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh old)
 (consumers : List (Atom Name)) (assignment : Name → Comp model)
 (valid : All model assignment (consumers ++ block old)) :
 All model (solve model fresh assignment) (rewrite old consumers ++ block fresh) := by
 obtain ⟨consumerValid,oldValid⟩ := (all_append model assignment consumers (block old)).mp valid
 apply (all_append model _ _ _).mpr
 refine ⟨?_,block_satisfied model laws.refl fresh freshSafe assignment⟩
 apply (rewrite_exact old consumers model _).mpr
 rw [solve_absorbs model old fresh oldSafe within assignment]
 exact (GeneralPresenceOrderedRecovery247.all_recovered model laws old assignment oldValid consumers).mpr consumerValid

theorem models_backward (model : Model) (laws : Laws model) (old fresh : List (Entry Name))
 (oldSafe : SafeOrder old) (consumers : List (Atom Name)) (assignment : Name → Comp model)
 (valid : All model assignment (rewrite old consumers ++ block fresh)) :
 All model (solve model old assignment) (consumers ++ block old) := by
 apply (all_append model _ _ _).mpr
 exact ⟨(rewrite_exact old consumers model assignment).mp ((all_append model _ _ _).mp valid).1,
   block_satisfied model laws.refl old oldSafe assignment⟩

theorem public_models_iff (model : Model) (laws : Laws model) (old fresh : List (Entry Name))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh old)
 (consumers : List (Atom Name)) (sharedNames : Name → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Name → Comp model) :
 (∃ assignment, All model assignment (consumers ++ block old) ∧ Agrees model sharedNames assignment boundary) ↔
 (∃ assignment, All model assignment (rewrite old consumers ++ block fresh) ∧ Agrees model sharedNames assignment boundary) := by
 constructor
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model fresh assignment,models_forward model laws old fresh oldSafe freshSafe within consumers assignment valid,?_⟩
   intro name shared
   rw [solve_outside model fresh assignment name]
   · exact agree name shared
   · intro entry member
     obtain ⟨original,present,equal⟩ := within entry member
     rw [← equal]
     exact privateTargets name shared original present
 · rintro ⟨assignment,valid,agree⟩
   refine ⟨solve model old assignment,models_backward model laws old fresh oldSafe consumers assignment valid,?_⟩
   intro name shared
   rw [solve_outside model old assignment name (privateTargets name shared)]
   exact agree name shared

theorem common_public_models_iff (old fresh : List (Entry Name))
 (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh) (within : TargetsWithin fresh old)
 (consumers : List (Atom Name)) (sharedNames : Name → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Name → Comp CommonNominalFullCarrier.model) :
 (∃ assignment, All CommonNominalFullCarrier.model assignment (consumers ++ block old) ∧
   Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) ↔
 (∃ assignment, All CommonNominalFullCarrier.model assignment (rewrite old consumers ++ block fresh) ∧
   Agrees CommonNominalFullCarrier.model sharedNames assignment boundary) :=
 public_models_iff _ GeneralPresenceCommonLaws245.common_laws old fresh oldSafe freshSafe within consumers sharedNames privateTargets boundary
end Yulang.GeneralPresenceOrderedRebase247
