import Yulang.GeneralDictionaryLooseFamilyReobserve240
import Yulang.GeneralDictionaryLooseFamilyFull240
set_option backward.isDefEq.respectTransparency false
/-! Actual replay-transformer bookkeeping, indexed independently of any
claimed reachable execution. Model validity of these atoms is proved by
induction from full versioned packet semantics. -/
namespace Yulang.GeneralDictionaryLooseIterationBook240
open GeneralDictionaryLooseLoopSource240 (roles model)
structure Book where
 allocated : List GeneralNominalIdentities.Origin
 reserved : List Nat
 ordinary : List (PresenceNormalForm.Atom Nat)
abbrev packetFor (n) (b : Book) := GeneralDictionaryLooseFamilyPacket240.packet n b.allocated b.reserved b.ordinary
abbrev planFor (n) (b : Book) := GeneralDictionaryLooseFamilyPacket240.plan n b.allocated b.reserved b.ordinary
def advance (n : Nat) (b : Book) : Book :=
 let state := (GeneralNominalVersionedInstallation231.replayPlan (planFor n b)).packet.context.state
 ⟨state.allocated,state.reserved,state.ordinary⟩
def book : Nat → Book
 | 0 => ⟨[],[],[]⟩
 | n+1 => advance n (book n)
abbrev allocations (n) := (book n).allocated
abbrev reservations (n) := (book n).reserved
abbrev atoms (n) := (book n).ordinary
abbrev packet (n) := packetFor n (book n)
abbrev plan (n) := planFor n (book n)
abbrev context (n) := (packet n).context

theorem atoms_valid (n) : PresenceNormalForm.All CommonNominalFullCarrier.model model (atoms n) := by
 induction n with
 | zero => intro _ h; cases h
 | succ n ih =>
   have full := GeneralDictionaryLooseFamilyFull240.packet_holds n (allocations n) (reservations n) (atoms n) ih
   have replay := (GeneralNominalVersionedInstallation231.replay_holds_iff (plan n) model).mpr full
   exact replay.1.2.2

theorem packet_holds (n) : GeneralNominalVersionedPlans231.Holds (plan n) model :=
 GeneralDictionaryLooseFamilyFull240.packet_holds n _ _ _ (atoms_valid n)

theorem allocated_next (n) : allocations (n+1) = allocations n ++ GeneralNominalVersionedInstallation231.allocated (packet n) := rfl
theorem reserved_next (n) : reservations (n+1) = reservations n ++ GeneralNominalVersionedInstallation231.reserved (packet n) := rfl
theorem atoms_next (n) : atoms (n+1) = atoms n ++ GeneralNominalVersionedInstallation231.atoms (packet n) := rfl

theorem base_zero : GeneralDictionaryLooseFamilyBase240.base 0 = GeneralDictionaryLooseLoopSource240.base := by
 unfold GeneralDictionaryLooseFamilyBase240.base GeneralDictionaryLooseLoopSource240.base
 congr 1
 · funext slot
   exact GeneralDictionaryLooseFamilyBase240.source_small slot slot.isLt
 · funext slot
   exact GeneralDictionaryLooseFamilyBase240.source_small slot slot.isLt

theorem context_zero : context 0 = GeneralDictionaryLooseLoopSource240.context := by
  dsimp [context,packet,packetFor,GeneralDictionaryLooseFamilyPacket240.packet,GeneralDictionaryLooseFamilySnapshot240.context]
  congr 1
  unfold GeneralDictionaryLooseFamilySnapshot240.snapshot GeneralDictionaryLooseLoopSource240.snapshot
  congr 1
  · exact base_zero
  · unfold GeneralDictionaryLooseFamilyBase240.view GeneralDictionaryLooseLoopSource240.view
    congr 1
    all_goals first | exact base_zero | exact proof_irrel_heq _ _ | rfl
  · funext slot
    change Fin 5 at slot
    have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 ∨ slot = 4 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl <;> rfl
  all_goals first | exact proof_irrel_heq _ _ | skip

theorem after_reobserve_context (journal : GeneralNominalVersionedJournal232.State roles) (n) :
 (GeneralNominalVersionedRefresh232.reobserve
   (GeneralDictionaryLooseFamilyReobserve240.refreshed allocations reservations atoms journal n)
   (GeneralDictionaryLooseFamilyReobserve240.revision allocations reservations atoms journal n)).core.erased.current.context = context (n+1) := rfl
end Yulang.GeneralDictionaryLooseIterationBook240
