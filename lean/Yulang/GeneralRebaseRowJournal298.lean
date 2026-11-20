import Yulang.GeneralRebaseRowClass298
import Yulang.GeneralRebaseRowObserved298
import Yulang.GeneralNominalRebaseJournalView243

namespace Yulang.GeneralRebaseRowJournal298
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243

def effectComponents (effect : Effect) : List (List Nat) :=
 [GeneralRebaseRowView298.support effect.raw,
  GeneralRebaseRowProjection298.support effect.projection,
  GeneralRebaseRowClass298.support effect.historical,
  GeneralRebaseRowClass298.support effect.live]

def effectReads (effect : Effect) : List Nat := (effectComponents effect).flatten

def components (journal : Journal) : List (List Nat) :=
 [GeneralRebaseRowView298.support journal.current,
  GeneralRebaseRowView298.support journal.source,
  journal.observed.flatMap GeneralRebaseRowObserved298.support,
  journal.sites.flatMap GeneralRebaseRowLive298.support,
  journal.packets.flatMap GeneralRebaseRowPacket298.support,
  journal.effects.flatMap effectReads]

def support (journal : Journal) : List Nat := (components journal).flatten

theorem effect_iff (effect : Effect) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ effectReads effect, (first n).2 = (last n).2) :
 effect.Holds first ↔ effect.Holds last := by
 have covered (reads : List Nat) (member : reads ∈ effectComponents effect) :
     ∀ n ∈ reads, (first n).2 = (last n).2 :=
   fun n h => rows n (List.mem_flatten.mpr ⟨reads,member,h⟩)
 apply and_congr (GeneralRebaseRowView298.models_iff effect.raw first last types
   (covered _ (by simp [effectComponents])))
 apply and_congr (GeneralRebaseRowProjection298.models_iff effect.projection first last types
   (covered _ (by simp [effectComponents])))
 exact and_congr (GeneralRebaseRowClass298.holds_iff effect.historical first last types
   (covered _ (by simp [effectComponents])))
   (GeneralRebaseRowClass298.holds_iff effect.live first last types
   (covered _ (by simp [effectComponents])))

theorem models_iff (journal : Journal) (first last : Assignment)
 (types : ∀ n, (first n).1 = (last n).1)
 (rows : ∀ n ∈ support journal, (first n).2 = (last n).2) :
 journal.Models first ↔ journal.Models last := by
 have covered (reads : List Nat) (member : reads ∈ components journal) :
     ∀ n ∈ reads, (first n).2 = (last n).2 :=
   fun n h => rows n (List.mem_flatten.mpr ⟨reads,member,h⟩)
 apply and_congr (GeneralRebaseRowView298.models_iff journal.current first last types
   (covered _ (by simp [components])))
 apply and_congr (GeneralRebaseRowView298.models_iff journal.source first last types
   (covered _ (by simp [components])))
 apply and_congr
 · apply forall_congr'; intro arguments
   apply forall_congr'; intro member
   exact GeneralRebaseRowObserved298.holds_iff arguments first last types
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨arguments,member,h⟩))
 apply and_congr
 · apply forall_congr'; intro site
   apply forall_congr'; intro member
   exact GeneralRebaseRowLive298.site_iff site first last types
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨site,member,h⟩))
 apply and_congr
 · apply forall_congr'; intro packet
   apply forall_congr'; intro member
   exact GeneralRebaseRowPacket298.packet_iff packet first last types
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨packet,member,h⟩))
 · apply forall_congr'; intro effect
   apply forall_congr'; intro member
   exact effect_iff effect first last types
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨effect,member,h⟩))
end Yulang.GeneralRebaseRowJournal298
