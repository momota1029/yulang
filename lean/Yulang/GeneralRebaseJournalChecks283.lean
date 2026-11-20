import Yulang.GeneralRebaseClassDelta283

namespace Yulang.GeneralRebaseJournalChecks283
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243 (Journal)
open GeneralNominalJournalSupport249 (effectReads effect_iff)
open Core.PresenceGeneration (CompTerm)

structure Check where
  reads : List Nat
  Holds : Assignment → Prop
  stable : ∀ a b, (∀ n, (a n).2 = (b n).2) →
    (∀ n ∈ reads, (a n).1 = (b n).1) → (Holds a ↔ Holds b)

def Checks (checks : List Check) (m : Assignment) : Prop := ∀ c ∈ checks, c.Holds m

def Checks.recheck (checks : List Check) (dirty : List Nat) (cache next : Assignment) : Prop :=
  ∀ c ∈ checks, if c.reads.any dirty.contains then c.Holds next else c.Holds cache

theorem stable_when (c : Check) (dirty : List Nat) (cache next : Assignment)
    (rows : ∀ n, (cache n).2 = (next n).2)
    (outside : ∀ n, n ∉ dirty → cache n = next n)
    (clean : ¬ c.reads.any dirty.contains = true) : c.Holds cache ↔ c.Holds next := by
  apply c.stable cache next rows
  intro n reads
  apply congrArg Prod.fst (outside n ?_)
  intro hit
  exact clean (List.any_eq_true.mpr ⟨n,reads,by simpa using hit⟩)

theorem recheck_exact (checks : List Check) (dirty : List Nat) (cache next : Assignment)
    (rows : ∀ n, (cache n).2 = (next n).2)
    (outside : ∀ n, n ∉ dirty → cache n = next n) :
    Checks.recheck checks dirty cache next ↔ Checks checks next := by
  unfold Checks.recheck Checks
  apply forall_congr'; intro c
  apply forall_congr'; intro _
  by_cases hit : c.reads.any dirty.contains = true
  · simp only [hit,ite_true]
  · rw [ite_eq_right hit]
    exact stable_when c dirty cache next rows outside hit

theorem reuse (checks : List Check) (dirty : List Nat) {cache next : Assignment}
    (rows : ∀ n, (cache n).2 = (next n).2)
    (outside : ∀ n, n ∉ dirty → cache n = next n)
    (known : Checks checks cache) :
    Checks checks next ↔ ∀ c ∈ checks, c.reads.any dirty.contains = true → c.Holds next := by
  rw [← recheck_exact checks dirty cache next rows outside]
  constructor
  · intro tests c member hit
    simpa only [Checks.recheck,hit,ite_true] using tests c member
  · intro changed c member
    by_cases hit : c.reads.any dirty.contains = true
    · simpa only [hit,ite_true] using changed c member hit
    · rw [ite_eq_right hit]; exact known c member

def raw (view : GeneralNominalRebaseRawView243.View) : Check :=
  ⟨GeneralNominalViewSupport249.support view,view.Models,GeneralNominalViewSupport249.models_iff view⟩
def observed (args : List GeneralNominalRebaseObservedSite243.Argument) : Check :=
  ⟨GeneralNominalObservedSupport249.support args,GeneralNominalRebaseObservedSite243.Holds args,
    GeneralNominalObservedSupport249.holds_iff args⟩
def center (site : GeneralNominalRebaseLiveView243.Site) : Check :=
  ⟨GeneralNominalLiveSupport249.support site,site.Holds,GeneralNominalLiveSupport249.site_iff site⟩
def packet (record : GeneralNominalRebasePacketView243.Packet) : Check :=
  ⟨GeneralNominalPacketSupport249.support record,record.Holds,GeneralNominalPacketSupport249.packet_iff record⟩
def effect (record : GeneralNominalRebaseJournalView243.Effect) : Check :=
  ⟨effectReads record,record.Holds,effect_iff record⟩

def checks (journal : Journal) : List Check :=
  [raw journal.current, raw journal.source] ++
  journal.observed.map observed ++ journal.sites.map center ++
  journal.packets.map packet ++ journal.effects.map effect

theorem checks_exact (journal : Journal) (m : Assignment) :
    Checks (checks journal) m ↔ journal.Models m := by
  simp only [Checks,checks,List.forall_mem_append,List.forall_mem_cons,List.not_mem_nil,
    false_implies,List.forall_mem_map,raw,observed,center,packet,effect,Journal.Models]
  have vacuous : (∀ _ : Check, True) ↔ True := ⟨fun _ => True.intro,fun _ _ => True.intro⟩
  simp only [and_assoc,vacuous,true_and]

end Yulang.GeneralRebaseJournalChecks283
