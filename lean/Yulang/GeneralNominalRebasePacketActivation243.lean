import Yulang.GeneralNominalRebasePacketSupport243
set_option backward.isDefEq.respectTransparency false
/-! Checked activation preserving a finite list of complete compiled packets.
The list is explicit; whole-journal enumeration is a separate obligation. -/
namespace Yulang.GeneralNominalRebasePacketActivation243
open GeneralNominalRebasePacketView243 (Packet)
open GeneralNominalRebasePacketSupport243 (sources models_iff)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalCommonBridge (Assignment)

def reads (packets : List Packet) : List Nat := packets.flatMap sources

def Checked (entries : List Entry) (packets : List Packet) : Prop :=
 ∀ entry ∈ entries, entry.1 ∉ reads packets

def check (entries : List Entry) (packets : List Packet) : Bool :=
 entries.all (fun entry => !(reads packets).contains entry.1)

theorem check_iff (entries : List Entry) (packets : List Packet) :
 check entries packets = true ↔ Checked entries packets := by simp [check,Checked]

def Holds (packets : List Packet) (model : Assignment) : Prop := ∀ packet ∈ packets, packet.Holds model

theorem holds_iff (entries : List Entry) (packets : List Packet) (checked : Checked entries packets)
 {first last : Assignment} (kept : Preserves entries first last) : Holds packets first ↔ Holds packets last := by
 apply forall_congr'; intro packet
 apply forall_congr'; intro member
 apply models_iff
 intro name present
 apply kept.1 name
 intro entry included equal
 apply checked entry included
 rw [equal]
 exact List.mem_flatMap.mpr ⟨packet,member,present⟩

theorem activate (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (packets : List Packet) (checked : Checked entries packets) (model : Assignment)
 (valid : Holds packets model) :
 Preserves entries (patch entries model) model ∧ Definitions entries (patch entries model) ∧
 Holds packets (patch entries model) :=
 ⟨patch_preserves entries model,patch_definitions entries coherent external model,
   (holds_iff entries packets checked (patch_preserves entries model)).mpr valid⟩

theorem projection_iff (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (packets : List Packet) (checked : Checked entries packets) (model : Assignment) :
 Holds packets model ↔ ∃ next, Preserves entries next model ∧ Definitions entries next ∧ Holds packets next := by
 constructor
 · intro valid
   exact ⟨patch entries model,activate entries coherent external packets checked model valid⟩
 · rintro ⟨next,kept,_,valid⟩
   exact (holds_iff entries packets checked kept).mp valid

theorem compiled_packets (entries : List Entry) (coherent : Coherent entries) (external : External entries)
 (plans : List (GeneralNominalCenters.Plan roles))
 (mapping : Nat → Core.PresenceGeneration.CompTerm Nat)
 (checked : Checked entries (plans.map (fun plan => GeneralNominalRebasePacketView243.compile plan mapping)))
 (model : Assignment)
 (valid : ∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan
   (GeneralNominalRebaseRawView243.read mapping model)) :
 ∃ next, Preserves entries next model ∧ Definitions entries next ∧
 ∀ plan ∈ plans, GeneralNominalVersionedPlans231.Holds plan
   (GeneralNominalRebaseRawView243.read mapping next) := by
 have packetsValid : Holds (plans.map (fun plan => GeneralNominalRebasePacketView243.compile plan mapping)) model := by
   intro packet member
   obtain ⟨plan,present,rfl⟩ := List.mem_map.mp member
   exact (GeneralNominalRebasePacketView243.compile_exact plan mapping model).mpr (valid plan present)
 obtain ⟨next,kept,definitions,packets⟩ :=
   (projection_iff entries coherent external _ checked model).mp packetsValid
 refine ⟨next,kept,definitions,?_⟩
 intro plan member
 exact (GeneralNominalRebasePacketView243.compile_exact plan mapping next).mp
   (packets _ (List.mem_map.mpr ⟨plan,member,rfl⟩))
end Yulang.GeneralNominalRebasePacketActivation243
