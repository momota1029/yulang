import Yulang.GeneralNominalPointKernel240
set_option backward.isDefEq.respectTransparency false
/-! Source-identity form of I45 preservation. Records retain both type and row
endpoint identities, constructor and declaration. This is not a bound on the
number of newly created, previously nonpoint descriptors or installations. -/
namespace Yulang.GeneralNominalPointRecord240
open GeneralNominalState (Parameter Descriptor)
open GeneralNominalReobservationSteps (PointDescriptor)

abbrev ParameterKey := Sum (Nat × Nat) (Nat × Nat)
structure Key where
 constructor : Nat
 declaration : GeneralDeclarationPatterns.Constructor
 arguments : List ParameterKey

def parameterKey (base : GeneralSourceState.State) : Parameter base.slots → ParameterKey
 | .type pair => .inl (base.source pair.1,base.source pair.2)
 | .row pair => .inr (base.rowSource pair.1,base.rowSource pair.2)
def key (base : GeneralSourceState.State) (descriptor : Descriptor base.slots) : Key :=
 ⟨descriptor.constructor,descriptor.declaration,descriptor.arguments.map (parameterKey base)⟩
def Recorded (snapshot : GeneralNominalState.State) (source : Nat) (value : Key) : Prop :=
 ∃ slot descriptor, snapshot.base.source slot = source ∧ snapshot.nominals slot = some descriptor ∧
 PointDescriptor descriptor ∧ key snapshot.base descriptor = value

theorem rename_point (embed : Fin first → Fin last) (point : PointDescriptor descriptor) :
 PointDescriptor (GeneralNominalRefinements.renameDescriptor embed descriptor) := by
 intro parameter member
 obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
 have equal := point old present
 cases old <;> simp only [GeneralNominalRefinements.renameParameter,GeneralNominalReobservationSteps.PointParameter] at equal ⊢
 all_goals exact congrArg embed equal

theorem key_rename (refinement : GeneralNominalRefinements.Refines before after) (descriptor : Descriptor before.base.slots) :
 key after.base (GeneralNominalRefinements.renameDescriptor refinement.base.embed descriptor) = key before.base descriptor := by
 unfold key GeneralNominalRefinements.renameDescriptor
 congr 1
 rw [List.map_map]
 apply List.map_congr_left
 intro parameter _
 cases parameter <;> simp only [Function.comp_apply,GeneralNominalRefinements.renameParameter,parameterKey,
   refinement.base.source,refinement.base.rowSource]

theorem refines (refinement : GeneralNominalRefinements.Refines before after)
 (held : Recorded before source value) : Recorded after source value := by
 obtain ⟨slot,descriptor,identity,found,point,same⟩ := held
 refine ⟨refinement.base.embed slot,GeneralNominalRefinements.renameDescriptor refinement.base.embed descriptor,
   (refinement.base.source slot).trans identity,refinement.nominals slot descriptor found,rename_point _ point,?_⟩
 exact (key_rename refinement descriptor).trans same

theorem reobserve (revision : GeneralNominalReobservationSteps.Revision (state : GeneralNominalSaturationState.State roles))
 (preserved : GeneralNominalPointRevision240.Preserves revision)
 (held : Recorded state.context.state source value) : Recorded revision.snapshot source value := by
 obtain ⟨slot,descriptor,identity,found,point,same⟩ := held
 exact ⟨slot,descriptor,identity,preserved slot descriptor found point,point,same⟩
end Yulang.GeneralNominalPointRecord240
