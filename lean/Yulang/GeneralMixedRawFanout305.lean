import Yulang.GeneralMixedReindexOutputHalt305
import Yulang.GeneralMixedReindexOutputCompiler305

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedRawFanout305
open GeneralDictionaryOutputDepth252 (registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralMixedReindexOutputFixture305 (widened other_refresh requests_both checked_deep_payload)
open GeneralMixedReindexOutputHalt305 (widened_halted)
open GeneralMixedReindexOutputCompiler305 (bits widened_valid actual_run)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedJournal232 (State)
open GeneralMixedDiagnosticHead304 (boundary8)

def firstTag (state : State roles) : Nat :=
  match (List.ofFn state.core.erased.current.context.state.view.shapes).head? with
  | some (.variant name) => name
  | _ => 0

theorem firstTag_widened (n : Nat) : firstTag (widened n) = n := rfl

theorem bounded_tags {xs : List Nat} {x : Nat} (member : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => cases member
  | cons a rest ih =>
    cases List.mem_cons.mp member with
    | inl equal => subst x; exact Nat.le_max_left ..
    | inr old => exact Nat.le_trans (ih old) (Nat.le_max_right ..)

/-- Even after restricting to strict refreshes that reach raw halts and pass
the same complete V8 input, a finite list of raw states cannot enumerate all
possible successors from this installed state. -/
theorem beyond_any_finite_list (enumerated : List (State roles)) :
    ∃ next, next ∉ enumerated ∧ Step registry root installed next ∧
      (∀ after, ¬ Step registry root next after) ∧
      GeneralRebaseDiagnosticData268.Valid (boundary8 roles) registry next root bits := by
  let tags := enumerated.map firstTag
  let n := tags.foldr Nat.max 0 + 1
  refine ⟨widened n,?_,other_refresh n,widened_halted n,widened_valid n⟩
  intro member
  have memory : n ∈ tags := by
    change n ∈ enumerated.map firstTag
    rw [← firstTag_widened n]
    exact List.mem_map_of_mem member
  have bounded := bounded_tags memory
  exact Nat.not_succ_le_self _ bounded

end Yulang.GeneralMixedRawFanout305
