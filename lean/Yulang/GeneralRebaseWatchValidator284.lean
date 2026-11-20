import Yulang.GeneralRebaseVersionWindowQueries284
import Yulang.GeneralRebaseLooseWindowQueries284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchValidator284
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseFutureWatch284 (Closed Covers)
open GeneralRebaseWatchStep284 (NoReveal next)
open GeneralRebaseSortedCache283 (Ascending push push_exact)
open GeneralNominalAcyclicEquations237 (Coherent)
open GeneralPresenceUsedSupport245 (typedReads)

def Bound (frontier : Nat) (defs : List (Entry Nat)) : Prop :=
  ∀ e ∈ defs, e.1 ≤ frontier

def high (seed : Nat) (rows : List (Entry Nat)) : Nat :=
  rows.foldl (fun n r => max n r.1) seed

theorem high_seed (seed : Nat) (rows : List (Entry Nat)) : seed ≤ high seed rows := by
  induction rows generalizing seed with
  | nil => exact Nat.le_refl _
  | cons h tail ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem high_covers (seed : Nat) (rows : List (Entry Nat)) : Bound (high seed rows) rows := by
  induction rows generalizing seed with
  | nil => intro _ h; cases h
  | cons h tail ih =>
    intro row seen
    rcases List.mem_cons.mp seen with rfl|found
    · exact Nat.le_trans (Nat.le_max_right _ _) (high_seed (max seed row.1) tail)
    · exact ih _ row found

def admits (frontier : Nat) (old new : List Nat) : Bool :=
  new.all (fun n => old.contains n || decide (frontier < n))

theorem admissible (frontier : Nat) (old new : List Nat) :
    admits frontier old new = true ↔ ∀ n ∈ new, n ∈ old ∨ frontier < n := by
  simp [admits]

theorem no_reveal {frontier : Nat} {old new : List Nat} {defs : List (Entry Nat)}
    (bound : Bound frontier defs) (safe : admits frontier old new = true) : NoReveal old new defs := by
  intro row found requested
  exact ((admissible _ _ _).mp safe _ requested).resolve_right
    (Nat.not_lt_of_ge (bound row found))

def checkRows (watch : List Nat) (rows : List (Entry Nat)) : Bool :=
  rows.all (fun row => (typedReads row.2).all watch.contains)

theorem check_sound (watch : List Nat) (rows : List (Entry Nat)) :
    checkRows watch rows = true ↔ ∀ e ∈ rows, typedReads e.2 ⊆ watch := by
  simp only [checkRows,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
  rfl

structure Compact where
  watermark : Nat
  watch : List Nat
  kept : List (Entry Nat)

def update (current : Compact) (new : List Nat) (delta : List (Entry Nat)) : Option Compact :=
  let rows := next new current.kept delta
  if admits current.watermark current.watch new && checkRows new rows then
    some ⟨high current.watermark delta,new,rows⟩
  else none

structure Valid (c : Compact) (full : List (Entry Nat)) : Prop where
  bound : Bound c.watermark full
  covers : Covers c.watch full c.kept
  sorted : Ascending c.kept

theorem checked {c d : Compact} {before full delta : List (Entry Nat)} {watch : List Nat}
    (old : Valid c before) (parts : ∀ e, e ∈ full ↔ e ∈ delta ∨ e ∈ before)
    (coherent : Coherent full) (ran : update c watch delta = some d) :
    Valid d full ∧ d.kept.length ≤ watch.length := by
  simp only [update] at ran
  split at ran
  · rename_i both
    obtain ⟨admission,rows⟩ := Bool.and_eq_true_iff.mp both
    have safe := no_reveal old.bound admission
    have fullClosed : Closed watch full := by
      intro e listed request
      have included (row : Entry Nat) (found : row ∈ delta ++ c.kept) : row ∈ full :=
        (parts row).mpr ((List.mem_append.mp found).imp id (fun h => old.covers.sound h))
      obtain ⟨_,pushed⟩ := push_exact delta c.kept old.sorted
        (fun a ha b hb eq => coherent a (included a ha) b (included b hb) eq)
      have retained : e ∈ next watch c.kept delta :=
        (GeneralRebaseFutureWatch284.member_exact ..).mpr
        ⟨(pushed e).mpr (((parts e).mp listed).imp id (fun m => old.covers.enough e m (safe e m request))),request⟩
      exact (check_sound watch _).mp rows e retained
    have contents := GeneralRebaseWatchStep284.advance old.covers old.sorted parts coherent fullClosed safe
    cases Option.some.inj ran
    refine ⟨⟨?_,contents.1,contents.2⟩,GeneralRebaseWatchStep284.length_limit contents.2⟩
    intro e listed
    rcases (parts e).mp listed with fresh|prior
    · exact high_covers _ _ e fresh
    · exact Nat.le_trans (old.bound e prior) (high_seed _ _)
  · cases ran

theorem local_only (c : Compact) (watch : List Nat) (delta : List (Entry Nat)) :
    update c watch delta = none ↔
      admits c.watermark c.watch watch = false ∨ checkRows watch (next watch c.kept delta) = false := by
  simp only [update]
  by_cases x : admits c.watermark c.watch watch = true <;>
    by_cases y : checkRows watch (next watch c.kept delta) = true <;>
    simp [x,y,Bool.eq_false_iff]

end Yulang.GeneralRebaseWatchValidator284
