import Yulang.GeneralVersionedSemanticPeer312

set_option backward.isDefEq.respectTransparency false
/-! A pointwise characterization of the smallest finite semantic support.
The result concerns full model validity, not the syntax of constraints. -/
namespace Yulang.GeneralVersionedEssentialSupport313
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedModelSupport237 (Support Observation)

abbrev Apart (key : Nat) (first last : Assignment) :=
  ∀ n, n ≠ key → first n = last n

def Inert (s : State roles) (key : Nat) : Prop :=
  ∀ first last, Apart key first last → (Models s first ↔ Models s last)

def Essential (s : State roles) (key : Nat) : Prop := ¬ Inert s key

theorem outside (supported : Support s names) (absent : key ∉ names) : Inert s key := by
  intro first last away
  exact supported first last (fun n member => away n (fun eq => absent (eq ▸ member)))

theorem must_mem (supported : Support s names) (active : Essential s key) : key ∈ names := by
  classical
  apply Classical.byContradiction
  intro hn
  exact active (outside supported hn)

noncomputable def trim (s : State roles) (names : List Nat) : List Nat := by
  classical
  exact names.filter (fun n => decide (Essential s n))

theorem mem_trim : key ∈ trim s names ↔ key ∈ names ∧ Essential s key := by
  classical
  simp [trim]

theorem patch_agreement (first last : Assignment) (key : Nat) :
    Apart key first (fun n => if n = key then last n else first n) := by
  intro n diff
  simp [diff]

theorem clear (s : State roles) (names : List Nat) (first last : Assignment)
    (same : Agree (trim s names) first last) :
    ∃ patched : Assignment, Agree names patched last ∧
      (∀ n, n ∉ names → patched n = first n) ∧ (Models s first ↔ Models s patched) := by
  classical
  induction names generalizing first with
  | nil => exact ⟨first,by simp [Agree],by simp,Iff.rfl⟩
  | cons key tail ih =>
    let p : Assignment := fun n => if n = key then last n else first n
    have truth : Models s first ↔ Models s p := by
      by_cases act : Essential s key
      · have keyEq := same key (mem_trim.mpr ⟨by simp,act⟩)
        suffices first = p by rw [← this]
        funext n
        by_cases eq : n = key
        · subst n
          simpa [p] using keyEq
        · simp [p,eq]
      · have h : Inert s key := Classical.byContradiction act
        exact h first p (patch_agreement first last key)
    have tailSame : Agree (trim s tail) p last := by
      intro n mem
      by_cases eq : n = key
      · simp [p,eq]
      · simpa [p,eq] using same n (mem_trim.mpr
          ⟨List.mem_cons_of_mem _ (mem_trim.mp mem).1,(mem_trim.mp mem).2⟩)
    obtain ⟨q,agrees,outside,thenTruth⟩ := ih p tailSame
    refine ⟨q,?_,?_,truth.trans thenTruth⟩
    · intro n mem
      rcases List.mem_cons.mp mem with equal | later
      · subst n
        by_cases inTail : key ∈ tail
        · exact agrees key inTail
        · simpa [p] using outside key inTail
      · exact agrees n later
    · intro n absent
      have diff : n ≠ key := fun h => absent (List.mem_cons.mpr (Or.inl h))
      have tailAbsent : n ∉ tail := fun h => absent (List.mem_cons_of_mem _ h)
      simpa [p,diff] using outside n tailAbsent

theorem trimmed (supported : Support s names) : Support s (trim s names) := by
  intro first last same
  obtain ⟨patch,agrees,_,truth⟩ := clear s names first last same
  exact truth.trans (supported patch last agrees)

theorem support_iff (hasSupport : Support s witness) :
    Support s names ↔ ∀ key, Essential s key → key ∈ names := by
  refine ⟨fun s _ => must_mem s,?_⟩
  intro all
  exact GeneralNominalVersionedModelSupport237.weaken (trimmed hasSupport)
    (fun _ h => all _ (mem_trim.mp h).2)

theorem observation (action : Observation before after) : Essential after key ↔ Essential before key := by
  have same := GeneralNominalVersionedModelSupport237.observation_models action
  unfold Essential Inert
  apply not_congr
  constructor
  · intro h first last apart
    exact (same first).symm.trans ((h first last apart).trans (same last))
  · intro h first last apart
    exact (same first).trans ((h first last apart).trans (same last).symm)

end Yulang.GeneralVersionedEssentialSupport313
