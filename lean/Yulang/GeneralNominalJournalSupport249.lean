import Yulang.GeneralNominalClassSupport249
import Yulang.GeneralNominalObservedSupport249
import Yulang.GeneralNominalRebaseJournalView243

/-! Explicit support of every actual compiled journal field, including both
historical and live class effects. This does not construct new source steps.
The bridge back to actual journal semantics separately requires LegacyEmpty. -/
namespace Yulang.GeneralNominalJournalSupport249
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243

def effectComponents (effect : Effect) : List (List Nat) :=
 [GeneralNominalViewSupport249.support effect.raw,
  GeneralNominalProjectionSupport249.support effect.projection,
  GeneralNominalClassSupport249.support effect.historical,
  GeneralNominalClassSupport249.support effect.live]

def effectReads (effect : Effect) : List Nat := (effectComponents effect).flatten

def components (journal : Journal) : List (List Nat) :=
 [GeneralNominalViewSupport249.support journal.current,
  GeneralNominalViewSupport249.support journal.source,
  journal.observed.flatMap GeneralNominalObservedSupport249.support,
  journal.sites.flatMap GeneralNominalLiveSupport249.support,
  journal.packets.flatMap GeneralNominalPacketSupport249.support,
  journal.effects.flatMap effectReads]

def support (journal : Journal) : List Nat := (components journal).flatten

theorem effect_iff (effect : Effect) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ effectReads effect, (first n).1 = (last n).1) :
 effect.Holds first ↔ effect.Holds last := by
 have covered (reads : List Nat) (member : reads ∈ effectComponents effect) :
     ∀ n ∈ reads, (first n).1 = (last n).1 :=
   fun n h => types n (List.mem_flatten.mpr ⟨reads,member,h⟩)
 apply and_congr (GeneralNominalViewSupport249.models_iff effect.raw first last rows
   (covered _ (by simp [effectComponents])))
 apply and_congr (GeneralNominalProjectionSupport249.models_iff effect.projection first last rows
   (covered _ (by simp [effectComponents])))
 exact and_congr (GeneralNominalClassSupport249.holds_iff effect.historical first last rows
   (covered _ (by simp [effectComponents])))
   (GeneralNominalClassSupport249.holds_iff effect.live first last rows
   (covered _ (by simp [effectComponents])))

theorem models_iff (journal : Journal) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support journal, (first n).1 = (last n).1) :
 journal.Models first ↔ journal.Models last := by
 have covered (reads : List Nat) (member : reads ∈ components journal) :
     ∀ n ∈ reads, (first n).1 = (last n).1 :=
   fun n h => types n (List.mem_flatten.mpr ⟨reads,member,h⟩)
 apply and_congr (GeneralNominalViewSupport249.models_iff journal.current first last rows
   (covered _ (by simp [components])))
 apply and_congr (GeneralNominalViewSupport249.models_iff journal.source first last rows
   (covered _ (by simp [components])))
 apply and_congr
 · apply forall_congr'; intro arguments
   apply forall_congr'; intro member
   exact GeneralNominalObservedSupport249.holds_iff arguments first last rows
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨arguments,member,h⟩))
 apply and_congr
 · apply forall_congr'; intro site
   apply forall_congr'; intro member
   exact GeneralNominalLiveSupport249.site_iff site first last rows
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨site,member,h⟩))
 apply and_congr
 · apply forall_congr'; intro packet
   apply forall_congr'; intro member
   exact GeneralNominalPacketSupport249.packet_iff packet first last rows
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨packet,member,h⟩))
 · apply forall_congr'; intro effect
   apply forall_congr'; intro member
   exact effect_iff effect first last rows
     (fun n h => covered _ (by simp [components]) n (List.mem_flatMap.mpr ⟨effect,member,h⟩))
end Yulang.GeneralNominalJournalSupport249
