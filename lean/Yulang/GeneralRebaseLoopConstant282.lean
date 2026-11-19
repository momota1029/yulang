import Yulang.GeneralRebaseLoopBase282

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralRebaseLoopConstant282
open Core.PresenceGeneration (TyTerm)
open GeneralRebaseLoopBase282
open GeneralRebaseHistoryOrder282 (history decode)
open GeneralRebaseTermAggregate281 (writes keys active expression address)
open GeneralRebaseTermCopy281 (Write Respects)
open GeneralRebaseLiveStore282 (live)
open GeneralRebaseWholeStore282 (store expression_exact)
open GeneralRebasePrivateKey282 (port)
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceOrderedSubstitution247 (mapping)
open CommonNominalFullCarrier (Equivalent model subtype_refl)
open GeneralRebaseAggregateCollapse281 (equivalence_retarget)

def pair (lo hi : Nat) (lower upper : TyTerm Nat) : List Write := [(lo,lower),(hi,upper)]

theorem pair_exact (lo hi : Nat) (lower upper : TyTerm Nat) (m : Assignment) :
    Respects (pair lo hi lower upper) m ↔
      Equivalent (m lo).1 (lower.eval model m) ∧ Equivalent (m hi).1 (upper.eval model m) := by
  constructor
  · intro recorded
    exact ⟨recorded _ List.mem_cons_self,recorded _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩
  · intro valid row found
    rcases List.mem_cons.mp found with rfl|other
    · exact valid.1
    · cases List.mem_singleton.mp other
      exact valid.2

namespace Version
open GeneralRebaseLoopBase282.Version (decode_reach newest_eq lower_chain)
open GeneralDictionaryVersionLoopNames238 (lower)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralDictionaryVersionLoopBook239 (packet plan)

def low := port 3 0 0 ⟨0,false,0⟩
def high := port 3 0 0 ⟨0,true,0⟩
def simple : List Write := pair low high (.var 2) (.var 2)
def olderLow (n : Nat) : TyTerm Nat := .union (.var (lower n)) (.var (lower n))
def olderHigh (n : Nat) : TyTerm Nat := .inter (.var (lower n)) (.var (lower n))

theorem writes_shape (n : Nat) : writes (packet n) true =
    pair low high (olderLow n) (olderHigh n) ++ pair low high (olderLow n) (olderHigh n) := by
  unfold writes keys active expression address
  change (([0,0] : List Nat).flatMap _).map _ = _
  simp only [GeneralDictionaryVersionLoopFamilyPacket238.bindings_exact]
  rfl

theorem newest_store (n : Nat) (base : Assignment) :
    Respects (live (state (n+1))) base ↔ Respects (store (state (n+1)) (packet n)) base := by
  rw [live,lists_all]
  constructor
  · intro everyone
    exact everyone (plan n) ((newest_eq n _).mpr rfl)
  · intro primary q known
    cases (newest_eq n _).mp known
    exact primary

theorem normalized_low (n : Nat) (base : Assignment) :
    Equivalent (((olderLow n).subst (mapping (history (state (n+1))))).eval model base) (base 2).1 := by
  rw [expression_exact]
  exact equiv_trans (union_same _) (lower_chain (n+1) n (by omega) base)

theorem normalized_high (n : Nat) (base : Assignment) :
    Equivalent (((olderHigh n).subst (mapping (history (state (n+1))))).eval model base) (base 2).1 := by
  rw [expression_exact]
  apply equiv_trans (inter_same _)
  exact lower_chain (n+1) n (by omega) base

theorem constant_exact (n : Nat) (m : Assignment) :
    Respects (live (state (n+1))) m ↔ Respects simple m := by
  rw [newest_store,store,writes_shape,GeneralPresenceDefinitionRewrite244.transform,List.map_append]
  change Respects (pair low high ((olderLow n).subst (mapping (history (state (n+1)))))
        ((olderHigh n).subst (mapping (history (state (n+1))))) ++
      pair low high ((olderLow n).subst (mapping (history (state (n+1)))))
        ((olderHigh n).subst (mapping (history (state (n+1)))))) m ↔ Respects simple m
  have duplicated (ws : List Write) : Respects (ws ++ ws) m ↔ Respects ws m := by
    constructor
    · exact fun held row used => held row (List.mem_append_left _ used)
    · intro held row used
      exact (List.mem_append.mp used).elim (held row) (held row)
  rw [duplicated,simple,pair_exact,pair_exact]
  exact and_congr (equivalence_retarget (normalized_low n m))
    (equivalence_retarget (normalized_high n m))

end Version

namespace Loose
open GeneralRebaseLoopBase282.Loose (decode_reach newest_eq lower_chain)
open GeneralDictionaryLooseFamilyNames240 (lower)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryLooseIterationBook240 (packet plan)

def low := port 4 0 0 ⟨0,false,0⟩
def high := port 4 0 0 ⟨0,true,0⟩
def simple : List Write := pair low high (.var 2) (.var 4)
def olderLow (n : Nat) : TyTerm Nat := .union (.var (lower n)) (.var (lower n))
def olderHigh (_n : Nat) : TyTerm Nat := .inter (.var (4)) (.var (4))

theorem writes_shape (n : Nat) : writes (packet n) true =
    pair low high (olderLow n) (olderHigh n) ++ pair low high (olderLow n) (olderHigh n) := by
  unfold writes keys active expression address
  change (([0,0] : List Nat).flatMap _).map _ = _
  simp only [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
  rfl

theorem newest_store (n : Nat) (base : Assignment) :
    Respects (live (state (n+1))) base ↔ Respects (store (state (n+1)) (packet n)) base := by
  rw [live,lists_all]
  constructor
  · intro everyone
    exact everyone (plan n) ((newest_eq n _).mpr rfl)
  · intro primary q known
    cases (newest_eq n _).mp known
    exact primary

theorem normalized_low (n : Nat) (base : Assignment) :
    Equivalent (((olderLow n).subst (mapping (history (state (n+1))))).eval model base) (base 2).1 := by
  rw [expression_exact]
  exact equiv_trans (union_same _) (lower_chain (n+1) n (by omega) base)

theorem normalized_high (n : Nat) (base : Assignment) :
    Equivalent (((olderHigh n).subst (mapping (history (state (n+1))))).eval model base) (base 4).1 := by
  rw [expression_exact]
  apply equiv_trans (inter_same _)
  have keep : GeneralRebaseWholeJournal282.Observable (state (n+1)) [4] :=
    (GeneralRebaseWholeJournal282.source_visibility (decode_reach (n+1)) [4] (by
      intro id listed
      cases List.mem_singleton.mp listed
      change 4 ≤ (state (n+1)).core.erased.current.context.state.seed
      rw [(stages (n+1)).shape.current]
      change 4 ≤ 4
      decide)).1
  have equality := congrArg Prod.fst
    (GeneralRebaseWholeJournal282.preserves_reads keep base 4 (List.mem_singleton_self _))
  change Equivalent (decode (state (n+1)) base 4).1 (base 4).1
  rw [equality]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem constant_exact (n : Nat) (m : Assignment) :
    Respects (live (state (n+1))) m ↔ Respects simple m := by
  rw [newest_store,store,writes_shape,GeneralPresenceDefinitionRewrite244.transform,List.map_append]
  change Respects (pair low high ((olderLow n).subst (mapping (history (state (n+1)))))
        ((olderHigh n).subst (mapping (history (state (n+1))))) ++
      pair low high ((olderLow n).subst (mapping (history (state (n+1)))))
        ((olderHigh n).subst (mapping (history (state (n+1)))))) m ↔ Respects simple m
  have duplicated (ws : List Write) : Respects (ws ++ ws) m ↔ Respects ws m := by
    constructor
    · exact fun held row used => held row (List.mem_append_left _ used)
    · intro held row used
      exact (List.mem_append.mp used).elim (held row) (held row)
  rw [duplicated,simple,pair_exact,pair_exact]
  exact and_congr (equivalence_retarget (normalized_low n m))
    (equivalence_retarget (normalized_high n m))

end Loose

end Yulang.GeneralRebaseLoopConstant282
