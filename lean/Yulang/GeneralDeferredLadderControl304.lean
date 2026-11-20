import Yulang.GeneralDeferredLadderClosed304
import Yulang.GeneralNominalKnownBit304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderControl304
open GeneralDeferredLadderRelay304 (Relay refPhase refState ctx)
open GeneralNominalKnownBit304 (knownBit known_exact)
open GeneralNominalVersionedJournal232 (State)
open GeneralDeclarationExamples (roles)
open GeneralObservedLadderJournalRows301 (site_count)

structure Control where
  index : Nat
  seen : Bool
  deriving DecidableEq, Repr

def view (n : Nat) (s : State roles) : Control :=
  ⟨s.core.erased.current.sites.length - 1, knownBit (ctx s).state (n+1)⟩

inductive Edge (n : Nat) : Control → Control → Prop
  | install (tag : Bool) (le : k ≤ n) : Edge n ⟨k,tag⟩ ⟨k+1,tag⟩
  | observe (cap : k ≤ n+1) : Edge n ⟨k,false⟩ ⟨k,true⟩

def successors (n : Nat) (c : Control) : List Control :=
  (if c.index ≤ n then [⟨c.index+1,c.seen⟩] else []) ++
  (if c.seen = false ∧ c.index ≤ n+1 then [⟨c.index,true⟩] else [])

theorem successors_exact (n : Nat) (c d : Control) :
    d ∈ successors n c ↔ Edge n c d := by
  constructor
  · intro member
    obtain ⟨k,tag⟩ := c
    unfold successors at member
    rcases List.mem_append.mp member with edge|observation
    · by_cases yes : k ≤ n
      · simp only [yes,ite_true,List.mem_singleton] at edge
        subst d
        exact .install tag yes
      · simp [yes] at edge
    · by_cases yes : tag = false ∧ k ≤ n+1
      · simp [yes] at observation
        subst d
        obtain rfl := yes.1
        exact .observe yes.2
      · simp [yes] at observation
  · intro next
    cases next with
    | install tag bound =>
      exact List.mem_append_left _ (by simp [bound])
    | observe cap =>
      exact List.mem_append_right _ (by simp [cap])

theorem ref_size (n k : Nat) (cap : k ≤ n+1) :
    (refState n k cap).core.erased.current.sites.length = k+1 := by
  rw [(refPhase n k cap).raw_eq,List.length_map,site_count]

theorem view_ref (n k : Nat) (cap : k ≤ n+1) :
    view n (refState n k cap) = ⟨k,false⟩ := by
  have none : knownBit (ctx (refState n k cap)).state (n+1) = false := by
    cases b : knownBit (ctx (refState n k cap)).state (n+1)
    · rfl
    · exact False.elim (GeneralDeferredLadderRefresh302.unknown (refPhase n k cap) ((known_exact ..).mp b))
  unfold view
  rw [ref_size n k cap,none]
  simp only [Nat.add_sub_cancel]

theorem view_relay {n k cap s} (rel : Relay n k cap s) :
    view n s = ⟨k,true⟩ := by
  have len : s.core.erased.current.sites.length = k+1 := by
    rw [← rel.view.raw.sites]
    exact ref_size n k cap
  unfold view
  rw [len,(known_exact ..).mpr rel.known]
  simp only [Nat.add_sub_cancel]

def remaining (n : Nat) (c : Control) : Nat :=
  n+1-c.index + if c.seen then 0 else 1

theorem edge_consumes_one {n : Nat} {c d : Control} (edge : Edge n c d) :
    remaining n d + 1 = remaining n c := by
  cases edge with
  | install tag k => cases tag <;> simp [remaining] <;> omega
  | observe cap => simp [remaining]

end Yulang.GeneralDeferredLadderControl304
