import Yulang.GeneralDictionaryDefaultCover208

/-! Explicit finite-fact budgets for traces. These are semantic upper bounds,
not a claim that enumerating the exponentially sized cover is efficient. -/
namespace Yulang.GeneralDictionaryDefaultRank208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralDictionaryDefaultFinite208
open GeneralNominalCenteredAccessibility (facts)
open GeneralNominalFiniteProgress (remaining)
variable {roles : Roles.RoleDecls} {start state : State roles}

inductive Counted (registry : Registry) (root : Occurrence roles) (start : State roles) :
    Nat → State roles → Prop
  | refl : Counted registry root start 0 start
  | tail : Counted registry root start n before → Step registry root before after →
      Counted registry root start (n+1) after

theorem steps (trace : Counted registry root start n state) :
    B4Target.Steps (Step registry root) start state := by
  induction trace with
  | refl => exact .refl
  | tail trace step ih => exact .tail ih step

theorem remaining_le_length (holds : S → F → Prop) (basis : List F) (state : S) :
    remaining holds basis state ≤ basis.length := by
  classical
  induction basis with
  | nil => exact Nat.le_refl _
  | cons fact rest ih =>
    change (if holds state fact then remaining holds rest state else remaining holds rest state+1) ≤ rest.length+1
    split <;> omega

theorem budget (cover : FiniteCover registry root (initial context root))
    (trace : Counted registry root (initial context root) n state) :
    n + remaining Holds (facts cover.signatures cover.sources cover.occurrences) state ≤
      remaining Holds (facts cover.signatures cover.sources cover.occurrences) (initial context root) := by
  induction trace with
  | refl => simp only [Nat.zero_add, Nat.le_refl]
  | tail trace step ih =>
    obtain ⟨fact,member,old,now⟩ := fresh_fact cover (steps trace) step
    have lower := GeneralNominalFiniteProgress.remaining_decreases Holds
      (facts cover.signatures cover.sources cover.occurrences)
      (fun fact => monotone step fact) member old now
    omega

theorem length_bound (cover : FiniteCover registry root (initial context root))
    (trace : Counted registry root (initial context root) n state) :
    n ≤ (facts cover.signatures cover.sources cover.occurrences).length := by
  have bound := budget cover trace
  have upper := remaining_le_length Holds
    (facts cover.signatures cover.sources cover.occurrences) (initial context root)
  omega

theorem selections_length (items : List α) :
    (GeneralDictionaryDefaultCodes208.selections items).length = 2 ^ items.length := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
    simp only [GeneralDictionaryDefaultCodes208.selections,List.length_append,List.length_map,
      List.length_cons,ih,Nat.pow_succ]
    omega

/-- A uniform finite budget for every permitted trace from one checked ground
source, produced rather than required as an additional hypothesis. -/
theorem ground_budget (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    ∃ budget : Nat, ∀ n state, Counted registry root (initial context root) n state → n ≤ budget := by
  let cover := GeneralDictionaryDefaultCover208.cover checked source
    (GeneralDictionaryDefaultAncestry208.ground_depth_bound source point ground coverage)
  exact ⟨(facts cover.signatures cover.sources cover.occurrences).length,
    fun _ _ trace => length_bound cover trace⟩

end Yulang.GeneralDictionaryDefaultRank208
