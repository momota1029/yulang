import Yulang.GeneralPresenceCrossRead244
namespace Yulang.GeneralPresenceOwnerTable244
open Core.PresenceGeneration
open PresenceNormalForm
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244
variable {Name Owner : Type} [DecidableEq Name] [DecidableEq Owner]

structure State (Name Owner : Type) where
 base : List (Atom Name)
 owners : List Owner
 entries : Owner → List (Entry Name)

def Models (state : State Name Owner) (model : Model) (assignment : Name → Comp model) : Prop :=
 All model assignment state.base ∧ ∀ owner ∈ state.owners, All model assignment (block (state.entries owner))

def Consumers (state : State Name Owner) (owner : Owner) (model : Model) (assignment : Name → Comp model) : Prop :=
 All model assignment state.base ∧
 ∀ other ∈ state.owners, other ≠ owner → All model assignment (block (state.entries other))

def rebase (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name)) : State Name Owner where
 base := state.base.map (atomSubst (substitution (state.entries owner)))
 owners := state.owners
 entries := fun other => if other = owner then fresh else transform (substitution (state.entries owner)) (state.entries other)

theorem rebase_at (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name)) :
 (rebase state owner fresh).entries owner = fresh := by simp [rebase]

theorem rebase_other (state : State Name Owner) (owner other : Owner) (fresh : List (Entry Name)) (different : other ≠ owner) :
 (rebase state owner fresh).entries other = transform (substitution (state.entries owner)) (state.entries other) := by
 simp [rebase,different]

theorem base_exact (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (model : Model) (assignment : Name → Comp model) :
 All model assignment (rebase state owner fresh).base ↔
 All model (fun name => (substitution (state.entries owner) name).eval model assignment) state.base := by
 simp only [rebase,All,List.forall_mem_map,atom_exact]

theorem models_exact (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (present : owner ∈ state.owners)
 (disjoint : ∀ other ∈ state.owners, other ≠ owner → DisjointTargets (state.entries owner) (state.entries other))
 (model : Model) (assignment : Name → Comp model) :
 Models (rebase state owner fresh) model assignment ↔
 All model assignment (block fresh) ∧ Consumers state owner model
   (fun name => (substitution (state.entries owner) name).eval model assignment) := by
 constructor
 · rintro ⟨base,owners⟩
   refine ⟨?_,(base_exact state owner fresh model assignment).mp base,?_⟩
   · simpa only [rebase_at] using owners owner present
   · intro other member different
     have valid := owners other member
     rw [rebase_other state owner other fresh different] at valid
     exact (owner_block_exact _ _ (disjoint other member different) model assignment).mp valid
 · rintro ⟨freshValid,base,others⟩
   refine ⟨(base_exact state owner fresh model assignment).mpr base,?_⟩
   intro other member
   by_cases same : other = owner
   · subst other
     simpa only [rebase_at] using freshValid
   · rw [rebase_other state owner other fresh same]
     exact (owner_block_exact _ _ (disjoint other member same) model assignment).mpr (others other member same)

def ExternalState (state : State Name Owner) : Prop := ∀ owner ∈ state.owners, External (state.entries owner)
def CoherentState (state : State Name Owner) : Prop := ∀ owner ∈ state.owners, Coherent (state.entries owner)

theorem rebase_external (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (oldExternal : ExternalState state) (freshExternal : External fresh)
 (cross : ∀ other ∈ state.owners, other ≠ owner → CrossRead (state.entries owner) (state.entries other)) :
 ExternalState (rebase state owner fresh) := by
 intro other member
 by_cases same : other = owner
 · subst other; simpa only [rebase_at] using freshExternal
 · rw [rebase_other state owner other fresh same]
   exact transformed_external _ _ (cross other member same) (oldExternal other member)

theorem rebase_coherent (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name))
 (oldCoherent : CoherentState state) (freshCoherent : Coherent fresh) :
 CoherentState (rebase state owner fresh) := by
 intro other member
 by_cases same : other = owner
 · subst other; simpa only [rebase_at] using freshCoherent
 · rw [rebase_other state owner other fresh same]
   exact transform_coherent _ (oldCoherent other member)

theorem owner_list (state : State Name Owner) (owner : Owner) (fresh : List (Entry Name)) :
 (rebase state owner fresh).owners = state.owners := rfl
end Yulang.GeneralPresenceOwnerTable244
