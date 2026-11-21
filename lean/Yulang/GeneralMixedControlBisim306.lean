import Yulang.GeneralMixedControlRealize306
import Yulang.GeneralMixedControlMask306

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedControlBisim306
open GeneralDictionaryOutputDepth252 (registry root roles)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralRebaseDepthPathRank285 (ActualPath Hop)
open GeneralMixedControlAtoms306 (BasicFacts ReachFacts reach_facts)
open GeneralMixedControlRealize306 (Target destination exact_known)
open GeneralMixedControlMask306
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known sources)
variable {a b : State roles}

inductive Observe (q : Fin 2) (a : State roles) : State roles → Prop
  | refresh (ctx : GeneralNominalCandidates.Context) (cert : Refresh a ctx)
      (present : q.val ∈ sources (snapshot a))
      (notYet : ¬ Known (snapshot a) q.val) (now : Known ctx.state q.val) :
      Observe q a (refresh a ctx)

theorem raw (v : ReachFacts a) : Step registry root a b ↔ ∃ q, Observe q a b := by
  constructor
  · intro taken
    have hop := (GeneralRebaseDepthPathRank285.exact v.anchor v.kept).mp taken
    cases hop with
    | refresh ctx cert n present old new =>
      have loc := GeneralRebaseDepthPathAnchor285.fresh_position v.anchor ctx cert n old new
      rcases loc with rfl|rfl
      · exact ⟨0,.refresh ctx cert present old new⟩
      · exact ⟨1,.refresh ctx cert present old new⟩
  · rintro ⟨q,obs⟩
    cases obs with
    | refresh ctx cert present old new => exact ⟨root,.root,.refresh root ctx cert q.val present old new⟩

theorem project_observe {q : Fin 2} (step : Observe q a b) :
    fire q (project a) (project b) = true := by
  cases step with
  | refresh ctx cert present old new =>
    apply (fire_exact _ _ _).mpr
    exact ⟨fun i yes => (bit _ i).mpr (cert.refines.known i.val ((bit _ i).mp yes)),
      (missing a q).mpr old,(bit _ q).mpr new⟩

theorem is_equal_of_bits {x y : Mask} (agree : ∀ i : Fin 2, get x i = true ↔ get y i = true) :
    x = y := by
  have values (i : Fin 2) : get x i = get y i := by
    have h := agree i
    cases hx : get x i <;> cases hy : get y i <;> simp [hx,hy] at h ⊢
  exact Mask.ext (values 0) (values 1)

def newBits (a : State roles) (goal : Mask) (i : Fin 2) : Bool :=
  !get (project a) i && get goal i

theorem newBits_exact (a : State roles) (goal : Mask) (i : Fin 2) :
    newBits a goal i = true ↔ get (project a) i = false ∧ get goal i = true := by
  unfold newBits
  cases get (project a) i <;> simp

theorem new_is_unknown (a : State roles) (goal : Mask) (i : Fin 2) (h : newBits a goal i = true) :
    ¬ Known (snapshot a) i.val := (missing a i).mp ((newBits_exact ..).mp h).1

def lift (v : BasicFacts a) (goal : Mask) : State roles :=
  destination v (newBits a goal) (new_is_unknown a goal)

theorem lift_projection (v : BasicFacts a) (goal : Mask)
    (incl : ∀ i : Fin 2, get (project a) i = true → get goal i = true) :
    project (lift v goal) = goal := by
  apply is_equal_of_bits
  intro i
  rw [bit]
  unfold lift
  rw [exact_known]
  constructor
  · rintro (old|⟨j,selected,source⟩)
    · exact incl i ((bit a i).mpr old)
    · have eq : j = i := Fin.ext source
      subst j
      exact ((newBits_exact ..).mp selected).2
  · intro yes
    cases status : get (project a) i with
    | false => exact Or.inr ⟨i,(newBits_exact ..).mpr ⟨status,yes⟩,rfl⟩
    | true => exact Or.inl ((bit a i).mp status)

theorem lift_observe (v : BasicFacts a) (goal : Mask) (q : Fin 2)
    (edge : fire q (project a) goal = true) : Observe q a (lift v goal) := by
  obtain ⟨mono,was,known⟩ := (fire_exact _ _ _).mp edge
  let pick := newBits a goal
  let fresh := new_is_unknown a goal
  let p := GeneralMixedControlRealize306.proposal v pick fresh
  let ctx := GeneralMixedCheckedPromotion306.context a p
  have yes : pick q = true := (newBits_exact ..).mpr ⟨was,known⟩
  have there : Known ctx.state q.val :=
    (exact_known v pick fresh q.val).mpr (Or.inr ⟨q,yes,rfl⟩)
  obtain ⟨slot,source,_,_⟩ := v.scalars q
  have member : q.val ∈ sources (snapshot a) :=
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨slot,source⟩)))
  exact .refresh ctx (GeneralMixedCheckedPromotion306.certify a p v.cache
    (GeneralMixedControlRealize306.recorded v pick fresh)) member (fresh q yes) there

theorem labelled (v : BasicFacts a) (goal : Mask) (q : Fin 2) :
    fire q (project a) goal = true ↔ ∃ b, Observe q a b ∧ project b = goal := by
  constructor
  · intro edge
    exact ⟨lift v goal,lift_observe v goal q edge,lift_projection v goal ((fire_exact _ _ _).mp edge).1⟩
  · rintro ⟨b,step,rfl⟩
    exact project_observe step

/-- Every abstract edge lifts from every actual reached representative, and
every raw edge projects. This reports class reachability, not equality of
representatives or all possible raw successors. -/
theorem unlabelled {len : Nat} (path : ActualPath installed a len) (goal : Mask) :
    moves (project a) goal = true ↔ ∃ b, Step registry root a b ∧ project b = goal := by
  have v := reach_facts path
  constructor
  · intro code
    obtain ⟨q,h⟩ := (moves_exact _ _).mp code
    obtain ⟨b,action,same⟩ := (labelled v.basic goal q).mp h
    exact ⟨b,(raw v).mpr ⟨q,action⟩,same⟩
  · rintro ⟨b,action,rfl⟩
    obtain ⟨q,obs⟩ := (raw v).mp action
    exact (moves_exact _ _).mpr ⟨q,project_observe obs⟩

end Yulang.GeneralMixedControlBisim306
