import Yulang.GeneralDictionaryInitialProjection257
namespace Yulang.GeneralDictionaryFiniteView257
open Core.PresenceGeneration
open GeneralDictionaryFiveSlot257 (view)
open GeneralPresenceSubstitutionSupport244 (typeSources)

def pool : List (TyTerm Nat) := [.var 0,.var 1,.var 2,.var 3,.var 4,.base .int]

theorem two_views (n : Nat) : view n = view 0 ∨ view n = view 1 := by
 cases n with
 | zero => exact Or.inl rfl
 | succ n => exact Or.inr (GeneralDictionaryFiveSlot257.stable n)

theorem terms_finite (n : Nat) : GeneralNominalViewTypeTerms255.terms (view n) ⊆ pool := by
 rcases two_views n with equal | equal <;> rw [equal]
 all_goals decide

theorem atoms_fixed (n : Nat) (side : GeneralPresenceCheckedNormal252.Side) (term : TyTerm Nat)
 (present : term ∈ GeneralNominalViewTypeTerms255.terms (view n)) :
 GeneralPresenceCheckedNormal252.prepare side pool term = some term := by
 have member := terms_finite n present
 simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 all_goals cases side <;> rfl

theorem no_private_type_reads (n name : Nat) (privateName : 4 < name) (term : TyTerm Nat)
 (present : term ∈ GeneralNominalViewTypeTerms255.terms (view n)) : name ∉ typeSources term := by
 have member := terms_finite n present
 simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at member
 rcases member with rfl | rfl | rfl | rfl | rfl | rfl
 all_goals simp only [typeSources,List.mem_cons,List.not_mem_nil,or_false]
 all_goals first | trivial | omega

theorem row_metadata (n : Nat) (index : Fin 5) : ((view n).slot index).row = .var index.val := rfl

/-- A measure seeing only this compact current View cannot strictly descend
on every completed old replay cycle. No source transition is changed here. -/
theorem no_strict_view_rank (rank : GeneralNominalRebaseRawView243.View → Nat) :
 ¬ ∀ n, rank (view (n+2)) < rank (view (n+1)) := by
 intro descending
 have impossible : rank (view 2) < rank (view 1) := descending 0
 rw [GeneralDictionaryFiveSlot257.stable 1] at impossible
 omega
end Yulang.GeneralDictionaryFiniteView257
