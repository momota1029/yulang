import Yulang.GeneralDeclarativeMixedEndpoint339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMixedTree339
open GeneralDeclarativeCompoundTree338
open GeneralDeclarativeCompoundInputs338 (oldAfter old_sound)
open GeneralDeclarationPatterns (Pattern Constructors normalize normalizeArgs variablesArgs)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWitnessHead334 (Argument argument_sound)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeCompoundBatch338 (Ticket minted)
open GeneralDeclarativeCompoundRoutes338 (dispatch dispatch_exact)
open GeneralDeclarativeCompoundPattern338 (peel variables_peel)
open GeneralDeclarativeGrowth327 (fits)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeStableReads329 (names_one)

mutual
inductive Node {done : Nat → Prop} (c : Constructors) (i : Interpretation)
    (keep : List Nat) : World done → Capture → Pattern → World done → List Span → Prop where
  | binder : Bounds w.state arg → Node c i keep w arg (.var n) w [(n,arg)]
  | projected (old : Argument w.source c i (names w.reads ++ keep) w.state arg raw after uses) :
      Node c i keep w arg (normalize raw) (oldAfter old) uses
  | record {w : World done} (ticket : Ticket w.source arg fs) :
      fs ≠ [] → peel pat = (fs,endPat) →
      dispatch fs (minted w.state w.reads keep ticket.jobs) = some (kids,residual) →
      Forest c i keep (advance w ticket keep) kids pending fieldUses →
      Node c i keep pending residual.2 endPat final tailUses →
      Node c i keep w arg pat final (fieldUses ++ tailUses)

inductive Forest {done : Nat → Prop} (c : Constructors) (i : Interpretation)
    (keep : List Nat) : World done → List (Entry × Pattern) → World done → List Span → Prop where
  | nil : Forest c i keep w [] w []
  | cons : Node c i keep w one.1.2 one.2 between current →
      Forest c i keep between rest final more →
      Forest c i keep w (one::rest) final (current++more)
end

theorem native_stage {w : World done} (ticket : Ticket w.source a f) : Sound keep w (advance w ticket keep) :=
  ⟨advance_grows ticket keep,fun m fit => ⟨_,GeneralDeclarativeOpenExec339.execute ticket m fit keep⟩⟩

theorem record_exact {w middle final : World done} (ticket : Ticket w.source arg fs)
    (shape : peel pat = (fs,endPat))
    (chosen : dispatch fs (minted w.state w.reads keep ticket.jobs) = some (kids,residual))
    (f : ForestExact keep (advance w ticket keep) kids middle first)
    (t : TreeExact keep middle endPat final last) :
    TreeExact keep w pat final (first++last) := by
  obtain ⟨front,nFront,frontBounds⟩ := f
  obtain ⟨back,nBack,backBounds⟩ := t
  have ordering := variables_peel pat
  rw [shape] at ordering
  have exactFields := routed_variables (dispatch_exact chosen).1
  refine ⟨chain (native_stage ticket) (chain front back),?_,?_⟩
  · rw [List.map_append,nFront,nBack,exactFields,ordering]
  · intro x h
    exact (List.mem_append.mp h).elim (fun known => fits back.1.1 (frontBounds x known)) (backBounds x)

theorem leaf_exact {w : World done} (read : Argument w.source c i (names w.reads ++ keep) w.state arg pat after uses) :
    TreeExact keep w (normalize pat) (oldAfter read) uses := by
  obtain ⟨_,head,values⟩ := argument_sound read (reflexive _)
  exact ⟨old_sound read,names_one head,values⟩

theorem exact_tree (found : Node c i keep w arg p v uses) : TreeExact keep w p v uses := by
  refine Node.rec (motive_1 := fun w _ p v uses _ => TreeExact keep w p v uses)
    (motive_2 := fun w ts v uses _ => ForestExact keep w ts v uses) ?_ ?_ ?_ ?_ ?_ found
  · intros; rename_i fit
    exact ⟨identity _ _,rfl,fun _ h => by cases List.mem_singleton.mp h; exact fit⟩
  · intros; apply leaf_exact <;> assumption
  · intros; apply record_exact <;> assumption
  · intros; exact ⟨identity _ _,rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
  · intros; apply combine_fields <;> assumption

theorem exact_forest (found : Forest c i keep w ts v uses) : ForestExact keep w ts v uses := by
  refine Forest.rec (motive_1 := fun w _ p v uses _ => TreeExact keep w p v uses)
    (motive_2 := fun w ts v uses _ => ForestExact keep w ts v uses) ?_ ?_ ?_ ?_ ?_ found
  · intros; rename_i fit
    exact ⟨identity _ _,rfl,fun _ h => by cases List.mem_singleton.mp h; exact fit⟩
  · intros; apply leaf_exact <;> assumption
  · intros; apply record_exact <;> assumption
  · intros; exact ⟨identity _ _,rfl,fun _ h => False.elim (List.not_mem_nil h)⟩
  · intros; apply combine_fields <;> assumption

/-- At a field of an already compiled enclosing record, recover the
ordinary approved-projection witness from the actual lower/upper
source match. This does not require the actual center to have a row. -/
theorem from_approved {w : World done}
    (found : GeneralDeclarativeEndpointProbe321.Matches (GeneralDeclarativeOrigins321.restriction w.source) c i a p)
    (domain : ∀ code, GeneralNominalCenteredHeadMatExpressions.translate c i (normalize p) = some code →
      GeneralDeclarativeArityPlan330.Shape code) (keep) :
    ∃ v used, Node c i keep w a (normalize p) v used := by
  obtain ⟨_,_,project⟩ := GeneralDeclarativeMixedEndpoint339.committed_argument found domain (names w.reads ++ keep)
  exact ⟨_,_,.projected project⟩

end Yulang.GeneralDeclarativeMixedTree339
