import Yulang.GeneralNominalRebasePacketView243
import Yulang.GeneralNominalRebaseProjectionSupport243
import Yulang.GeneralNominalRebaseSchemaSupport243
import Yulang.GeneralNominalRebaseEffectActivation243
set_option backward.isDefEq.respectTransparency false
/-! Complete finite support of the materialized total packet meaning. -/
namespace Yulang.GeneralNominalRebasePacketSupport243
open GeneralNominalRebasePacketView243
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalRebaseViewActivation243 (siteSources argumentSources site_same)
open GeneralNominalRebaseEffectActivation243 (equationSources equation_iff)

def childSources (child : Child) : List Nat :=
 siteSources child.site ++ child.equations.flatMap equationSources

def blocks (packet : Packet) : List (List Nat) :=
 [GeneralNominalRebaseViewSupport243.sources packet.raw,
  packet.ordinary.flatMap GeneralNominalState.atomSources,
  GeneralNominalRebaseProjectionSupport243.reportSources packet.projection,
  siteSources packet.input,
  packet.binders.flatMap argumentSources,
  GeneralNominalRebaseSchemaSupport243.schemaSources packet.head,
  packet.children.flatMap childSources,
  packet.outputs.flatMap equationSources]

def sources (packet : Packet) : List Nat := (blocks packet).flatten

theorem argument_iff (argument : GeneralNominalRebaseLiveView243.Argument) {first last : Assignment}
 (same : Agree (argumentSources argument) first last) : argument.Holds first ↔ argument.Holds last := by
 have lower := GeneralNominalCenteredModelExtension.type_eval_same argument.lower
   (fun name member => same name (List.mem_append_left _ (List.mem_append_left _ member)))
 have upper := GeneralNominalCenteredModelExtension.type_eval_same argument.upper
   (fun name member => same name (List.mem_append_left _ (List.mem_append_right _ member)))
 have center := GeneralNominalCenteredModelExtension.type_eval_same argument.center
   (fun name member => same name (List.mem_append_right _ member))
 unfold GeneralNominalRebaseLiveView243.Argument.Holds
 rw [lower,upper,center]

theorem equations_iff (equations : List GeneralNominalRebaseEffectView243.Equation) {first last : Assignment}
 (same : Agree (equations.flatMap equationSources) first last) :
 AllEquations equations first ↔ AllEquations equations last := by
 apply forall_congr'; intro equation
 apply forall_congr'; intro member
 exact equation_iff equation (fun name present => same name (List.mem_flatMap.mpr ⟨equation,member,present⟩))

theorem child_iff (child : Child) {first last : Assignment}
 (same : Agree (childSources child) first last) : child.Holds first ↔ child.Holds last :=
 and_congr (site_same child.site (fun name member => same name (List.mem_append_left _ member)))
   (equations_iff child.equations (fun name member => same name (List.mem_append_right _ member)))

theorem models_iff (packet : Packet) {first last : Assignment}
 (same : Agree (sources packet) first last) : packet.Holds first ↔ packet.Holds last := by
 have field (block : List Nat) (member : block ∈ blocks packet) : Agree block first last :=
   fun name present => same name (List.mem_flatten.mpr ⟨block,member,present⟩)
 have raw := GeneralNominalRebaseViewSupport243.models_iff packet.raw (field _ (by simp [blocks]))
 have ordinary : PresenceNormalForm.All CommonNominalFullCarrier.model first packet.ordinary ↔
   PresenceNormalForm.All CommonNominalFullCarrier.model last packet.ordinary := by
   apply forall_congr'; intro atom
   apply forall_congr'; intro member
   exact GeneralNominalCenteredModelExtension.atom_same atom (fun name present =>
     field _ (by simp [blocks]) name (List.mem_flatMap.mpr ⟨atom,member,present⟩))
 have projection := GeneralNominalRebaseProjectionSupport243.models_iff packet.projection (field _ (by simp [blocks]))
 have input := site_same packet.input (field _ (by simp [blocks]))
 have binders : (∀ argument ∈ packet.binders, argument.Holds first) ↔
   (∀ argument ∈ packet.binders, argument.Holds last) := by
   apply forall_congr'; intro argument
   apply forall_congr'; intro member
   exact argument_iff argument (fun name present =>
     field _ (by simp [blocks]) name (List.mem_flatMap.mpr ⟨argument,member,present⟩))
 have head := GeneralNominalRebaseSchemaSupport243.models_iff packet.head (field _ (by simp [blocks]))
 have children : (∀ child ∈ packet.children, child.Holds first) ↔
   (∀ child ∈ packet.children, child.Holds last) := by
   apply forall_congr'; intro child
   apply forall_congr'; intro member
   exact child_iff child (fun name present =>
     field _ (by simp [blocks]) name (List.mem_flatMap.mpr ⟨child,member,present⟩))
 have outputs := equations_iff packet.outputs (field _ (by simp [blocks]))
 exact and_congr raw (and_congr ordinary (and_congr projection (and_congr input
   (and_congr binders (and_congr head (and_congr children outputs))))))

theorem compiled_iff (plan : GeneralNominalCenters.Plan roles)
 (mapping : Nat → Core.PresenceGeneration.CompTerm Nat) {first last : Assignment}
 (same : Agree (sources (compile plan mapping)) first last) :
 GeneralNominalVersionedPlans231.Holds plan (GeneralNominalRebaseRawView243.read mapping first) ↔
 GeneralNominalVersionedPlans231.Holds plan (GeneralNominalRebaseRawView243.read mapping last) :=
 (compile_exact plan mapping first).symm.trans ((models_iff (compile plan mapping) same).trans
   (compile_exact plan mapping last))
end Yulang.GeneralNominalRebasePacketSupport243
