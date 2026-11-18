import Yulang.GeneralNominalViewSupport249
import Yulang.GeneralNominalLiveSupport249
import Yulang.GeneralNominalProjectionSupport249
import Yulang.GeneralNominalSchemaSupport249
import Yulang.GeneralNominalEffectSupport249
import Yulang.GeneralNominalOrderedPacket248

/-! Explicit finite typed support for all eight components of actual compiled
Packet.Holds. Live outputs are additionally covered for value preservation.
No claim of enumeration of an operational journal is made. -/
namespace Yulang.GeneralNominalPacketSupport249
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebasePacketView243
open GeneralPresenceConsumerSupport246

def equationReads (equations : List GeneralNominalRebaseEffectView243.Equation) : List Nat :=
 equations.flatMap GeneralNominalEffectSupport249.equationReads

def childReads (child : Child) : List Nat :=
 GeneralNominalLiveSupport249.support child.site ++ equationReads child.equations

def components (packet : Packet) : List (List Nat) :=
 [GeneralNominalViewSupport249.support packet.raw,
  listTypedReads packet.ordinary,
  GeneralNominalProjectionSupport249.support packet.projection,
  GeneralNominalLiveSupport249.support packet.input,
  packet.binders.flatMap GeneralNominalLiveSupport249.argumentReads,
  GeneralNominalSchemaSupport249.support packet.head,
  packet.children.flatMap childReads,
  equationReads packet.outputs]

def support (packet : Packet) : List Nat := (components packet).flatten

theorem equations_iff (equations : List GeneralNominalRebaseEffectView243.Equation)
 (first last : Assignment) (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ equationReads equations, (first n).1 = (last n).1) :
 AllEquations equations first ↔ AllEquations equations last := by
 apply forall_congr'; intro equation
 apply forall_congr'; intro member
 exact GeneralNominalEffectSupport249.equation_iff equation first last rows
   (fun n h => types n (List.mem_flatMap.mpr ⟨equation,member,h⟩))

theorem child_iff (child : Child) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ childReads child, (first n).1 = (last n).1) :
 child.Holds first ↔ child.Holds last :=
 and_congr (GeneralNominalLiveSupport249.site_iff child.site first last rows
   (fun n h => types n (List.mem_append_left _ h)))
   (equations_iff child.equations first last rows (fun n h => types n (List.mem_append_right _ h)))

theorem packet_iff (packet : Packet) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support packet, (first n).1 = (last n).1) :
 packet.Holds first ↔ packet.Holds last := by
 have covered (reads : List Nat) (member : reads ∈ components packet) :
     ∀ n ∈ reads, (first n).1 = (last n).1 :=
   fun n h => types n (List.mem_flatten.mpr ⟨reads,member,h⟩)
 unfold Packet.Holds
 apply and_congr (GeneralNominalViewSupport249.models_iff packet.raw first last rows
   (covered _ (by simp [components])))
 apply and_congr (GeneralPresenceConsumerSupport246.all_iff model first last rows packet.ordinary
   (covered _ (by simp [components])))
 apply and_congr (GeneralNominalProjectionSupport249.models_iff packet.projection first last rows
   (covered _ (by simp [components])))
 apply and_congr (GeneralNominalLiveSupport249.site_iff packet.input first last rows
   (covered _ (by simp [components])))
 apply and_congr
 · apply forall_congr'; intro argument
   apply forall_congr'; intro member
   exact GeneralNominalLiveSupport249.argument_iff argument first last rows
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨argument,member,h⟩))
 apply and_congr (GeneralNominalSchemaSupport249.schema_iff packet.head first last rows
   (covered _ (by simp [components])))
 apply and_congr
 · apply forall_congr'; intro child
   apply forall_congr'; intro member
   exact child_iff child first last rows
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨child,member,h⟩))
 · exact equations_iff packet.outputs first last rows (covered _ (by simp [components]))
end Yulang.GeneralNominalPacketSupport249
