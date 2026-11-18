import Yulang.GeneralNominalMixedSchema251
/-! Total packet representation with old context and current capture reads.
Actual construction of the two maps is a separate obligation. -/
namespace Yulang.GeneralNominalMixedPacket251
open Core.PresenceGeneration (CompTerm)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan)
open GeneralNominalRebaseRawView243 (read)
open GeneralNominalRebasePacketView243 (Packet AllEquations equations children names binder)
open CommonNominalFullCarrier

def ordinary (plan : Plan roles) : List (PresenceNormalForm.Atom Nat) :=
 GeneralNominalAllocation.cross plan.packet.bindings ++
 GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)

def Ordinary (plan : Plan roles) (old : Assignment) : Prop :=
 GeneralNominalAllocation.Compatible plan.packet.bindings old ∧
 PresenceNormalForm.All model old
   (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet))

theorem ordinary_exact (plan : Plan roles) (old : Assignment) :
 PresenceNormalForm.All model old (ordinary plan) ↔ Ordinary plan old := by
 unfold ordinary Ordinary
 rw [PresenceNormalForm.all_append,GeneralNominalAllocation.cross_exact]

def Holds (plan : Plan roles) (old current : Assignment) : Prop :=
 GeneralNominalState.Models plan.packet.context.state old ∧
 Ordinary plan old ∧
 GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) old ∧
 plan.input.Holds old ∧
 (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
   GeneralNominalCaptureMerges.Fits current ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
     (current (GeneralNominalVersionedFrame231.binder plan name)).1) ∧
 GeneralNominalMixedSchema251.Holds plan plan.headSchema old current ∧
 (∀ clause ∈ plan.packet.declaration.requirements, ∀ valid : clause.Signature roles,
   (GeneralNominalVersionedFrame231.childSite plan clause valid).Holds current ∧
   (GeneralNominalVersionedPlans231.childSchema plan clause valid).Holds
     (GeneralNominalVersionedPlans231.variables plan current) current) ∧
 (GeneralNominalVersionedPlans231.emittedSchema plan).Holds (GeneralNominalVersionedPlans231.variables plan current) current

def compile (plan : Plan roles) (old current : Nat → CompTerm Nat) : Packet :=
 ⟨GeneralNominalRebaseRawView243.compile plan.packet.context.state old,
 (ordinary plan).map (GeneralNominalRebaseRawView243.atom old),
 GeneralNominalRebaseProjectionView243.compile plan.packet.context.state old (GeneralNominalPacketSupport.report plan.packet),
 GeneralNominalRebaseLiveView243.compile plan.input old,(names plan).map (binder plan current),
 GeneralNominalMixedSchema251.compile plan old current plan.headSchema,children plan current,
 equations plan current (GeneralNominalVersionedPlans231.emittedSchema plan)⟩

theorem compile_exact (plan : Plan roles) (old current : Nat → CompTerm Nat) (assignment : Assignment) :
 (compile plan old current).Holds assignment ↔ Holds plan (read old assignment) (read current assignment) := by
 unfold compile Packet.Holds Holds
 rw [GeneralNominalRebaseRawView243.compile_exact,GeneralNominalRebaseRawView243.all_exact,ordinary_exact,
   GeneralNominalRebaseProjectionView243.compile_exact,GeneralNominalRebaseLiveView243.compile_holds,
   GeneralNominalRebasePacketView243.binders_exact,GeneralNominalMixedSchema251.compile_exact,
   GeneralNominalRebasePacketView243.children_exact,GeneralNominalRebasePacketView243.equations_exact]
 rfl

/-- This compiler emits no legacy aggregate merge equations in ordinary.
The owner definition block must independently supply the new snapshot equations. -/
theorem ordinary_size (plan : Plan roles) (old current : Nat → CompTerm Nat) :
 (compile plan old current).ordinary.length =
 (GeneralNominalAllocation.cross plan.packet.bindings).length +
 (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)).length := by
 simp only [compile,List.length_map,ordinary,List.length_append]

theorem child_count (plan : Plan roles) (old current : Nat → CompTerm Nat) :
 (compile plan old current).children.length = plan.packet.declaration.requirements.length := by
 simp [compile,children]
end Yulang.GeneralNominalMixedPacket251
