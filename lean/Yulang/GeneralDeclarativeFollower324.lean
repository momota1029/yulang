import Yulang.GeneralDeclarativeHiddenPath324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFollower324
open GeneralDeclarativeHiddenDecl324 (registry interpretation parent checked)
open GeneralDeclarativeHiddenState324
open GeneralDeclarativeHiddenProbe324 (source_row root_bounds safe tests)
open GeneralDeclarativeExampleSource320 (point leaf int)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (restriction from_completed backed_iff)
open GeneralDeclarativeLowerKnown321 (Alias Knows Ready Delayed alias_refl knows_alias knows_row ready_iff_not_delayed)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeNFResolve324 (Rule)
open GeneralDeclarativeHiddenResolve324 (branch)
open GeneralDeclarativeEntailment320 (literal)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify All₂ Dictionary)

abbrev later : Demand := ⟨2,[point 6],[]⟩

theorem restriction_rows (completed : Nat → Prop) (eq : Equation) :
    eq ∈ (restriction (support completed)).equations ↔
      eq ∈ s0Rows ∨ (eq = parentRow ∧ completed 1) ∨ (eq = childRow ∧ completed 2) := by
  rw [backed_iff]
  constructor
  · rintro ⟨origin,caused,available⟩
    rcases caused with (has | ⟨contains,rfl⟩)
    · rcases has with (input | ⟨contains,rfl⟩)
      · exact .inl input.1
      · cases available with
        | completed c => exact .inr (.inl ⟨List.mem_singleton.mp contains,c⟩)
    · cases available with
      | completed c => exact .inr (.inr ⟨List.mem_singleton.mp contains,c⟩)
  · rintro (old | ⟨rfl,parentDone⟩ | ⟨rfl,childDone⟩)
    · exact ⟨.source,.inl (.inl ⟨old,rfl⟩),.source⟩
    · exact ⟨.output 1,.inl (.inr ⟨List.mem_cons_self,rfl⟩),.completed parentDone⟩
    · exact ⟨.output 2,.inr ⟨List.mem_cons_self,rfl⟩,.completed childDone⟩

theorem closed_alias (done : Nat → Prop) (cut : Nat → Prop)
    (edges : ∀ a b, (⟨a,.variable b⟩ : Equation) ∈ (restriction (support done)).equations →
      (cut a ↔ cut b))
    (alias : Alias (restriction (support done)) x y) : cut x ↔ cut y := by
  have diag {a b} (h : GeneralDeclarativeBounds319.Bound (restriction (support done)).normal a b) : a = b := by
    induction h with
    | refl => rfl
    | interval no => cases no
    | constraint no => cases no
    | trans _ _ x y => exact x.trans y
  induction alias with
  | bounds h _ => rw [diag h]
  | forward e => exact edges _ _ e
  | backward e => exact (edges _ _ e).symm
  | trans _ _ a b => exact a.trans b

theorem ready_both (done : Nat → Prop) (parentDone : done 1) (childDone : done 2) :
    Ready (support done) later := by
  intro arg found
  cases List.mem_singleton.mp found
  have ep := (restriction_rows done parentRow).mpr (.inr (.inl ⟨rfl,parentDone⟩))
  have ec := (restriction_rows done childRow).mpr (.inr (.inr ⟨rfl,childDone⟩))
  exact ⟨_,knows_alias (.trans (.forward ep) (.forward ec)) (knows_row
    (source_row done (show (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ s0Rows by simp [s0Rows])) rfl)⟩

theorem exclude (done : Nat → Prop) (cut : Nat → Prop)
    (edges : ∀ a b, (⟨a,.variable b⟩ : Equation) ∈ (restriction (support done)).equations → (cut a ↔ cut b))
    (start : cut 6) (off0 : ¬cut 0) (off2 : ¬cut 2) (off3 : ¬cut 3) :
    ¬Ready (support done) later := by
  intro outcome
  obtain ⟨tag,row,present,aliases,shape⟩ := outcome (point 6) List.mem_cons_self
  have impossible := (closed_alias done cut edges aliases).mp start
  rcases (restriction_rows done row).mp present with base|⟨rfl,_⟩|⟨rfl,_⟩
  · simp only [s0Rows,List.mem_cons,List.not_mem_nil,or_false] at base
    rcases base with rfl|rfl|rfl|rfl
    · exact off0 impossible
    · exact off0 impossible
    · exact off2 impossible
    · exact off3 impossible
  · cases shape
  · cases shape

theorem ready_iff (done : Nat → Prop) : Ready (support done) later ↔ done 1 ∧ done 2 := by
  constructor
  · intro h
    classical
    constructor
    · apply Classical.byContradiction
      intro absent
      apply exclude done (fun n => n = 6) ?_ rfl (by decide +kernel) (by decide +kernel) (by decide +kernel) h
      intro a b e
      rcases (restriction_rows done _).mp e with old|⟨_,impossible⟩|⟨same,_⟩
      · simp only [s0Rows,List.mem_cons,List.not_mem_nil,or_false] at old
        rcases old with h|h|h|h <;> cases h
      · exact False.elim (absent impossible)
      · cases same
        decide +kernel
    · apply Classical.byContradiction
      intro absent
      apply exclude done (fun n => n = 6 ∨ n = 5) ?_ (.inl rfl)
        (by decide +kernel) (by decide +kernel) (by decide +kernel) h
      intro a b e
      rcases (restriction_rows done _).mp e with old|⟨same,_⟩|⟨_,impossible⟩
      · simp only [s0Rows,List.mem_cons,List.not_mem_nil,or_false] at old
        rcases old with h|h|h|h <;> cases h
      · cases same
        decide +kernel
      · exact False.elim (absent impossible)
  · rintro ⟨p,c⟩
    exact ready_both done p c

/-- On the stabilized state the follower is already int in every
ordinary model. The separate source support rule still controls whether
an input-head read can use that fact. -/
theorem ordinary_value (m : Assignment) (valid : Models final m) :
    Equivalent (m 6).1 int := by
  obtain ⟨s0,out,child⟩ := (final_models m).mp valid
  have initialScalar := s0.2 ⟨3,.primitive (.scalar .int) []⟩ (by simp [initial,s0Rows])
  exact eqv_trans out (eqv_trans child initialScalar)

end Yulang.GeneralDeclarativeFollower324
