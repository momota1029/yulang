import Yulang.GeneralMixedCheckedPromotion306

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 12000000
namespace Yulang.GeneralMixedControlRealize306
open GeneralDictionaryOutputDepth252 (registry root roles)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralMixedControlAtoms306 (BasicFacts)
open GeneralMixedCheckedPromotion306 (Promotion context updated certify known_exact)
open GeneralNominalVersionedMixedObservations233 (Justified)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalState (Known)

variable {a : State roles}

def Target (pick : Fin 2 → Bool) (n : Nat) : Prop := ∃ q : Fin 2, pick q = true ∧ q.val = n

def choose (pick : Fin 2 → Bool) (i : Fin (snapshot a).base.slots) : Bool :=
  let n := (snapshot a).base.source i
  (decide (n = 0) && pick 0) || (decide (n = 1) && pick 1)

theorem chose (pick : Fin 2 → Bool) (i : Fin (snapshot a).base.slots) :
    choose pick i = true ↔ Target pick ((snapshot a).base.source i) := by
  simp only [choose,Bool.or_eq_true_iff,Bool.and_eq_true_iff,decide_eq_true_eq,Target]
  constructor
  · rintro (⟨source,yes⟩ | ⟨source,yes⟩)
    · exact ⟨0,yes,source.symm⟩
    · exact ⟨1,yes,source.symm⟩
  · rintro ⟨q,yes,eq⟩
    have small : q.val = 0 ∨ q.val = 1 := by omega
    rcases small.imp (Fin.ext (b := 0)) (Fin.ext (b := 1)) with rfl|rfl
    · exact Or.inl ⟨eq.symm,yes⟩
    · exact Or.inr ⟨eq.symm,yes⟩

def proposal (v : BasicFacts a) (pick : Fin 2 → Bool)
    (fresh : ∀ q, pick q = true → ¬ Known (snapshot a) q.val) : Promotion (snapshot a) where
  choose := choose pick
  plain := by
    intro i yes
    obtain ⟨q,wanted,source⟩ := (chose pick i).mp yes
    cases observed : (snapshot a).nominals i with
    | none => rfl
    | some d => exact (fresh q wanted ⟨i,source.symm,Or.inr ⟨d,observed⟩⟩).elim
  checks := by
    intro i yes
    obtain ⟨q,_,source⟩ := (chose pick i).mp yes
    obtain ⟨slot,named,lower,upper⟩ := v.scalars q
    have same := (snapshot a).base.source_injective (source.symm.trans named.symm)
    subst slot
    exact .ordinary lower upper

theorem recorded (v : BasicFacts a) (pick : Fin 2 → Bool)
    (fresh : ∀ q, pick q = true → ¬ Known (snapshot a) q.val)
    (i : Fin (snapshot a).base.slots) (yes : (proposal v pick fresh).choose i = true) :
    Justified a (.normalized (snapshot a).base i (.base .int)) := by
  obtain ⟨q,_,source⟩ := (chose pick i).mp yes
  refine ⟨[],[],.source,.source,fun m _ basic => ?_⟩
  have scalar := (GeneralRebaseDepthGroundModels285.source_inputs m).mp (v.origin ▸ basic.1)
  change CommonNominalFullCarrier.Equivalent (m ((snapshot a).base.source i)).1 (.base .int)
  rw [← source]
  have loc : q.val = 0 ∨ q.val = 1 := by omega
  rcases loc with e|e
  · rw [e]
    exact scalar.1
  · rw [e]
    exact scalar.2.1

def destination (v : BasicFacts a) (pick : Fin 2 → Bool)
    (fresh : ∀ q, pick q = true → ¬ Known (snapshot a) q.val) : State roles :=
  refresh a (context a (proposal v pick fresh))

theorem exact_known (v : BasicFacts a) (pick : Fin 2 → Bool)
    (fresh : ∀ q, pick q = true → ¬ Known (snapshot a) q.val) (n : Nat) :
    Known (snapshot (destination v pick fresh)) n ↔ Known (snapshot a) n ∨ Target pick n := by
  change Known (updated (proposal v pick fresh)) n ↔ _
  rw [known_exact]
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨i,yes,source⟩
    exact source ▸ (chose pick i).mp yes
  · rintro ⟨q,wanted,name⟩
    obtain ⟨i,source,_,_⟩ := v.scalars q
    exact ⟨i,(chose pick i).mpr ⟨q,wanted,source.symm⟩,source.trans name⟩

theorem actual (v : BasicFacts a) (pick : Fin 2 → Bool)
    (fresh : ∀ q, pick q = true → ¬ Known (snapshot a) q.val) (q : Fin 2) (wanted : pick q = true) :
    Step registry root a (destination v pick fresh) := by
  obtain ⟨slot,source,_,_⟩ := v.scalars q
  have member : q.val ∈ GeneralNominalState.sources (snapshot a) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨slot,source⟩)))
  exact ⟨root,.root,.refresh root (context a (proposal v pick fresh))
    (certify a (proposal v pick fresh) v.cache (recorded v pick fresh)) q.val member
    (fresh q wanted) ((exact_known v pick fresh q.val).mpr (Or.inr ⟨q,wanted,rfl⟩))⟩

end Yulang.GeneralMixedControlRealize306
