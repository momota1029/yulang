import Yulang.GeneralMixedCompoundTail307
import Yulang.GeneralNominalKnownBit304

namespace Yulang.GeneralMixedCompoundTailPresentation307
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryCompoundRefresh239 (refreshed)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperSnapshot307 (upper_known upper_unknown)
open GeneralMixedCompoundUpperRefresh307 (upperState step cert)
open GeneralMixedCompoundTail307 (AtTail exact_anchor every_successor_halted)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalKnownBit304 (knownBit known_exact)
open GeneralFiniteRawPresentation306 (Presentation StrongRaw)

def bit (s : State roles) : Bool := knownBit s.core.erased.current.context.state upper

def targets : Bool → List Bool
  | false => [true]
  | true => []

def nodes : List Bool := [false,true]

theorem anchor_bit : bit refreshed = false := by
  cases eq : bit refreshed
  · rfl
  · exact False.elim (upper_unknown ((known_exact ..).mp eq))

theorem next_bit {s : State roles} (act : Step registry root refreshed s) : bit s = true := by
  obtain ⟨ctx,_,known,rfl⟩ := exact_anchor.mp act
  exact (known_exact ..).mpr known

theorem upper_bit : bit upperState = true := next_bit step

theorem terminal_bit {ctx} (known : GeneralNominalState.Known ctx.state upper) :
    bit (refresh refreshed ctx) = true :=
  (known_exact ..).mpr known

theorem all {s : State roles} (live : AtTail s) (b : Bool) :
    b ∈ targets (bit s) ↔ ∃ t, Step registry root s t ∧ bit t = b := by
  rcases live with rfl|⟨ctx,⟨given⟩,known,rfl⟩
  · rw [anchor_bit]
    refine ⟨?_,?_⟩
    · intro h; cases List.mem_singleton.mp h; exact ⟨upperState,step,upper_bit⟩
    · rintro ⟨t,go,code⟩
      exact List.mem_singleton.mpr (code.symm.trans (next_bit go))
  · rw [terminal_bit known]
    constructor
    · intro h; cases h
    · rintro ⟨t,go,_⟩; exact (every_successor_halted ctx given known t go).elim

theorem present (paint : Bool → β) : Presentation AtTail (Step registry root) bit
    (fun s => paint (bit s)) targets paint nodes := by
  refine ⟨?_,?_,?_,fun _ _ => rfl,fun _ live _ => all live _⟩
  · intro a ha b hb
    cases b <;> simp [nodes]
  · intro s hs
    cases bit s <;> simp [nodes]
  · intro s t live go
    rcases live with rfl|⟨ctx,⟨given⟩,known,rfl⟩
    · exact Or.inr (exact_anchor.mp go)
    · exact False.elim (every_successor_halted ctx given known t go)

theorem has_next {s : State roles} (live : AtTail s) :
    (∃ t, Step registry root s t) ↔ bit s = false := by
  constructor
  · rintro ⟨t,go⟩
    have e := (all live (bit t)).mpr ⟨t,go,rfl⟩
    cases h : bit s
    · rfl
    · rw [h] at e; cases e
  · intro eq
    have listed : true ∈ targets (bit s) := by rw [eq]; exact List.mem_singleton_self _
    obtain ⟨t,go,_⟩ := (all live true).mp listed
    exact ⟨t,go⟩

theorem two_necessary {β : Type} {paint : State roles → β} {rel : State roles → State roles → Prop}
    (strong : StrongRaw AtTail (Step registry root) paint rel)
    {s t} (ls : AtTail s) (lt : AtTail t) (same : rel s t) :
    bit s = bit t := by
  have pair := strong s t ls lt same
  have enabled : (∃ x, Step registry root s x) ↔ (∃ y, Step registry root t y) :=
    ⟨fun ⟨x,go⟩ => let ⟨y,edge,_⟩ := pair.2.1 x go; ⟨y,edge⟩,
      fun ⟨y,go⟩ => let ⟨x,edge,_⟩ := pair.2.2 y go; ⟨x,edge⟩⟩
  have eq : bit s = false ↔ bit t = false :=
    (has_next ls).symm.trans (enabled.trans (has_next lt))
  cases hs : bit s <;> cases ht : bit t <;> simp_all

theorem actual_two : bit refreshed ≠ bit upperState ∧ AtTail refreshed ∧ AtTail upperState := by
  refine ⟨?_,Or.inl rfl,Or.inr (exact_anchor.mp step)⟩
  rw [anchor_bit,upper_bit]; decide

/-- Exact quotient only for the C239 tail and every actual immediate successor.
No converse is being claimed for the entire C238 source trace. -/
theorem exact_tail_minimum : Nonempty (Presentation AtTail (Step registry root) bit
      (fun _ => ()) targets (fun _ => ()) nodes) ∧
    ∀ rel, StrongRaw AtTail (Step registry root) (fun _ => ()) rel → ¬ rel refreshed upperState := by
  refine ⟨⟨present (fun _ => ())⟩,?_⟩
  intro rel b h
  exact actual_two.1 (two_necessary b actual_two.2.1 actual_two.2.2 h)

end Yulang.GeneralMixedCompoundTailPresentation307
