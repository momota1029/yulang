import Yulang.GeneralPresenceOrderedRefreshSequence247
import Yulang.GeneralPresenceOrderedSyntax247
/-! Once an ordered block has been expanded into consumers, refreshes whose
private target sets stay within that block cannot expand those consumers again.
This is a literal syntax invariant, not just model equivalence. The definitions
may still grow, and this is not a solver termination proof. -/
namespace Yulang.GeneralPresenceOrderedRefreshSyntax247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceOrderedSubstitution247 GeneralPresenceOrderedDependence247
open GeneralPresenceOrderedRefreshSequence247 GeneralPresenceOrderedSyntax247
variable {Name : Type} [DecidableEq Name]

omit [DecidableEq Name] in
theorem within_trans (first middle last : List (Entry Name))
 (one : TargetsWithin first middle) (two : TargetsWithin middle last) : TargetsWithin first last := by
 intro entry member
 obtain ⟨mid,inMiddle,equal⟩ := one entry member
 obtain ⟨final,inLast,other⟩ := two mid inMiddle
 exact ⟨final,inLast,other.trans equal⟩

theorem run_expanded (old : List (Entry Name)) (safe : SafeOrder old)
 (current : List (Entry Name)) (within : TargetsWithin current old)
 (atoms : List (Atom Name)) (updates : List (List (Entry Name)))
 (valid : ValidSteps current updates) :
 (run ⟨current,rewrite old atoms⟩ updates).consumers = rewrite old atoms := by
 induction updates generalizing current with
 | nil => rfl
 | cons fresh rest ih =>
   obtain ⟨_,nextWithin,tail⟩ := valid
   change (run ⟨fresh,rewrite current (rewrite old atoms)⟩ rest).consumers = _
   rw [rewrite_absorbs old current safe within]
   exact ih fresh (within_trans fresh current old nextWithin within) tail

theorem first_refresh_stabilizes (state : State Name) (safe : SafeOrder state.definitions)
 (fresh : List (Entry Name)) (rest : List (List (Entry Name)))
 (valid : ValidSteps state.definitions (fresh::rest)) :
 (run state (fresh::rest)).consumers = rewrite state.definitions state.consumers := by
 obtain ⟨_,within,tail⟩ := valid
 exact run_expanded state.definitions safe fresh within state.consumers rest tail
end Yulang.GeneralPresenceOrderedRefreshSyntax247
