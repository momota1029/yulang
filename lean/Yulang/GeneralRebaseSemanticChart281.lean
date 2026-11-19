import Yulang.GeneralRebasePortBatch280

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSemanticChart281

variable {V F S : Type}

def Entails (fact : F → V → Prop) (models : S → V → Prop) (s : S) (f : F) : Prop :=
  ∀ v, models s v → fact f v

def Complete (pool : List F) (fact : F → V → Prop) (models : S → V → Prop) (s : S) : Prop :=
  ∀ v, models s v ↔ ∀ f ∈ pool, Entails fact models s f → fact f v

def Loss (models : S → V → Prop) (old new : S) : Prop :=
  ∃ v, models old v ∧ ¬ models new v

def Gain (pool : List F) (fact : F → V → Prop) (models : S → V → Prop) (old new : S) : Prop :=
  ∃ f ∈ pool, ¬ Entails fact models old f ∧ Entails fact models new f

def Decreases (models : S → V → Prop) (old new : S) : Prop :=
  ∀ v, models new v → models old v

theorem entailment_mono {fact : F → V → Prop} {models : S → V → Prop} {old new : S}
    (restrict : Decreases models old new) :
    ∀ f, Entails fact models old f → Entails fact models new f :=
  fun _ already v good => already v (restrict v good)

theorem gain_cuts {pool : List F} {fact : F → V → Prop} {models : S → V → Prop} {old new : S}
    (gain : Gain pool fact models old new) : Loss models old new := by
  classical
  obtain ⟨f,_,notOld,new⟩ := gain
  apply Classical.byContradiction
  intro none
  apply notOld
  intro v held
  apply Classical.byContradiction
  intro absent
  exact none ⟨v,held,fun good => absent (new v good)⟩

theorem cut_gains {pool : List F} {fact : F → V → Prop} {models : S → V → Prop} {old new : S}
    (exactChart : Complete pool fact models new) (loss : Loss models old new) :
    Gain pool fact models old new := by
  classical
  obtain ⟨v,oldHeld,rejected⟩ := loss
  apply Classical.byContradiction
  intro none
  apply rejected ((exactChart v).mpr ?_)
  intro f heard new
  apply Classical.byContradiction
  intro lacks
  exact none ⟨f,heard,(fun h => lacks (h v oldHeld)),new⟩

theorem loss_iff_gain {pool : List F} {fact : F → V → Prop} {models : S → V → Prop} {old new : S}
    (exactChart : Complete pool fact models new) :
    Loss models old new ↔ Gain pool fact models old new :=
  ⟨cut_gains exactChart,gain_cuts⟩

theorem exact_of_requirements {pool obligations : List F} {fact : F → V → Prop}
    {models : S → V → Prop} {state : S} (included : obligations ⊆ pool)
    (defining : ∀ v, models state v ↔ ∀ f ∈ obligations, fact f v) :
    Complete pool fact models state := by
  intro v
  constructor
  · exact fun m _ _ h => h v m
  · intro consequence
    apply (defining v).mpr
    intro f h
    exact consequence f (included h) (fun w model => (defining w).mp model f h)

theorem exact_with_base {pool obligations : List F} {fact : F → V → Prop}
    {models : S → V → Prop} {state : S} {base : V → Prop}
    (impliesBase : ∀ v, models state v → base v)
    (included : obligations ⊆ pool)
    (defining : ∀ v, base v → (models state v ↔ ∀ f ∈ obligations, fact f v)) :
    ∀ v, base v → (models state v ↔ ∀ f ∈ pool, Entails fact models state f → fact f v) := by
  intro v within
  constructor
  · exact fun m _ _ h => h v m
  · intro key
    apply (defining v within).mpr
    intro f h
    exact key f (included h) (fun w model => (defining w (impliesBase w model)).mp model f h)

theorem relative_loss_iff {pool : List F} {fact : F → V → Prop} {models : S → V → Prop}
    {old new : S} {base : V → Prop} (domain : ∀ v, models old v → base v)
    (exactChart : ∀ v, base v →
      (models new v ↔ ∀ f ∈ pool, Entails fact models new f → fact f v)) :
    Loss models old new ↔ Gain pool fact models old new := by
  classical
  refine ⟨?_,gain_cuts⟩
  rintro ⟨v,held,lost⟩
  apply Classical.byContradiction
  intro none
  apply lost ((exactChart v (domain v held)).mpr ?_)
  intro f known fresh
  apply Classical.byContradiction
  intro failed
  exact none ⟨f,known,(fun h => failed (h v held)),fresh⟩

end Yulang.GeneralRebaseSemanticChart281
