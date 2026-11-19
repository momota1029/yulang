import Yulang.FiniteBehaviorDriver269

namespace Yulang.FiniteBehaviorKeyGraph269
open FiniteRankBehavior269 (Code Tracks)
open FiniteBehaviorSimulation269 (covers backs)
open FiniteBehaviorDriver269 (Advances)

structure Graph (n : Nat) (Label : Type) where
 label : Fin n → Label
 adj : Fin n → List (Fin n)
 cost : Label → Nat

def rank (g : Graph n Label) (i : Fin n) : Nat := g.cost (g.label i)

def valid (g : Graph n Label) : Bool :=
 (List.finRange n).all fun i => (g.adj i).all fun j => decide (rank g j < rank g i)

theorem valid_exact (g : Graph n Label) :
 valid g = true ↔ ∀ i, ∀ j ∈ g.adj i, rank g j < rank g i := by
 simp [valid,List.all_eq_true]

/-- Executable tree expansion on supplied finite weak keys. Rank validation
makes the fuel complete; this does not discover keys from arbitrary syntax. -/
def compile (g : Graph n Label) : Nat → Fin n → Code Label
 | 0,i => .node (g.label i) []
 | fuel+1,i => .node (g.label i) ((g.adj i).map (compile g fuel))

structure Realizes (g : Graph n Label) (key : Source → Fin n)
 (observe : Source → Label) (weak : Source → Source → Prop) : Prop where
 label : ∀ source, observe source = g.label (key source)
 forward : ∀ before after, weak before after → key after ∈ g.adj (key before)
 lift : ∀ source j, j ∈ g.adj (key source) → ∃ after, weak source after ∧ key after = j

theorem tracks (g : Graph n Label) (checked : valid g = true)
 (key : Source → Fin n) (observe : Source → Label) (weak : Source → Source → Prop)
 (spec : Realizes g key observe weak) (fuel : Nat) (source : Source)
 (enough : rank g (key source) ≤ fuel) :
 Tracks observe weak fuel source (compile g fuel (key source)) := by
 induction fuel generalizing source with
 | zero =>
   refine ⟨spec.label _,rfl,?_⟩
   intro after step
   have small := (valid_exact g).mp checked _ _ (spec.forward source after step)
   omega
 | succ fuel ih =>
   refine ⟨spec.label _,?_,?_⟩
   · intro after step
     have hit := spec.forward source after step
     have lt := (valid_exact g).mp checked _ _ hit
     exact ⟨compile g fuel (key after),List.mem_map.mpr ⟨_,hit,rfl⟩,ih after (by omega)⟩
   · intro code listed
     obtain ⟨j,adjacent,rfl⟩ := List.mem_map.mp listed
     obtain ⟨after,step,located⟩ := spec.lift source j adjacent
     have lt := (valid_exact g).mp checked _ _ adjacent
     exact ⟨after,step,located ▸ ih after (by rw [located]; omega)⟩

theorem sound_child (g : Graph n Label) (checked : valid g = true)
 (key : Source → Fin n) (observe : Source → Label) (weak : Source → Source → Prop)
 (spec : Realizes g key observe weak) (fuel : Nat) (source : Source) (enough : rank g (key source) ≤ fuel)
 (target : Code Label) :
 Advances (compile g fuel (key source)) target →
 ∃ after, weak source after ∧ Tracks observe weak fuel after target :=
 backs (tracks g checked key observe weak spec fuel source enough)

theorem covers_from_source (g : Graph n Label) (checked : valid g = true)
 (key : Source → Fin n) (observe : Source → Label) (weak : Source → Source → Prop)
 (spec : Realizes g key observe weak) (fuel : Nat) (source after : Source)
 (enough : rank g (key source) ≤ fuel) (step : weak source after) :
 ∃ target, Advances (compile g fuel (key source)) target ∧ Tracks observe weak fuel after target :=
 covers (tracks g checked key observe weak spec fuel source enough) step

end Yulang.FiniteBehaviorKeyGraph269
