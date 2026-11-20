import Yulang.GeneralRebaseRowView298
import Yulang.GeneralRebaseRowLive298
import Yulang.GeneralRebaseRowProjection298
import Yulang.GeneralRebaseRowSchema298
import Yulang.GeneralNominalEffectSupport249
import Yulang.GeneralNominalOrderedPacket248

namespace Yulang.GeneralRebaseRowPacket298
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebasePacketView243
open GeneralRebaseRowBasis298

def equationReads (equations : List GeneralNominalRebaseEffectView243.Equation) : List Nat :=
 equations.flatMap GeneralRebaseFiniteRowReads285.equationRows

def childReads (child : Child) : List Nat :=
 GeneralRebaseRowLive298.support child.site ++ equationReads child.equations

def components (packet : Packet) : List (List Nat) :=
 [GeneralRebaseRowView298.support packet.raw,
  listRowReads packet.ordinary,
  GeneralRebaseRowProjection298.support packet.projection,
  GeneralRebaseRowLive298.support packet.input,
  packet.binders.flatMap GeneralRebaseRowLive298.argumentReads,
  GeneralRebaseRowSchema298.support packet.head,
  packet.children.flatMap childReads,
  equationReads packet.outputs]

def support (packet : Packet) : List Nat := (components packet).flatten

theorem equations_iff (equations : List GeneralNominalRebaseEffectView243.Equation)
 (first last : Assignment) (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ equationReads equations, (first n).2 = (last n).2) :
 AllEquations equations first ↔ AllEquations equations last := by
 apply forall_congr'; intro equation
 apply forall_congr'; intro member
 exact GeneralRebaseRowBasis298.equation_iff equation first last types
   (fun n h => rows n (List.mem_flatMap.mpr ⟨equation,member,h⟩))

theorem child_iff (child : Child) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ childReads child, (first n).2 = (last n).2) :
 child.Holds first ↔ child.Holds last :=
 and_congr (GeneralRebaseRowLive298.site_iff child.site first last types
   (fun n h => rows n (List.mem_append_left _ h)))
   (equations_iff child.equations first last types (fun n h => rows n (List.mem_append_right _ h)))

theorem packet_iff (packet : Packet) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support packet, (first n).2 = (last n).2) :
 packet.Holds first ↔ packet.Holds last := by
 have covered (reads : List Nat) (member : reads ∈ components packet) :
     ∀ n ∈ reads, (first n).2 = (last n).2 :=
   fun n h => rows n (List.mem_flatten.mpr ⟨reads,member,h⟩)
 unfold Packet.Holds
 apply and_congr (GeneralRebaseRowView298.models_iff packet.raw first last types
   (covered _ (by simp [components])))
 apply and_congr (GeneralRebaseRowBasis298.all_iff model first last types packet.ordinary
   (covered _ (by simp [components])))
 apply and_congr (GeneralRebaseRowProjection298.models_iff packet.projection first last types
   (covered _ (by simp [components])))
 apply and_congr (GeneralRebaseRowLive298.site_iff packet.input first last types
   (covered _ (by simp [components])))
 apply and_congr
 · apply forall_congr'; intro argument
   apply forall_congr'; intro member
   exact GeneralRebaseRowLive298.argument_iff argument first last types
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨argument,member,h⟩))
 apply and_congr (GeneralRebaseRowSchema298.schema_iff packet.head first last types
   (covered _ (by simp [components])))
 apply and_congr
 · apply forall_congr'; intro child
   apply forall_congr'; intro member
   exact child_iff child first last types
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨child,member,h⟩))
 · exact equations_iff packet.outputs first last types (covered _ (by simp [components]))
end Yulang.GeneralRebaseRowPacket298
