import Yulang.GeneralDeclarativeI65B6TreeActualMeaning400

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂ Dictionary Frontier Resolves)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessTree349 (dictionaryTree dictionaryForest)

/-- The independent rule attests the actual pre-output frame; a
dictionary key alone is not such authority. No language rule is
implemented by this abstract interface. -/
abbrev FrameChoice400 := (s : State) → (q : Request) → AuthoredBodyFrame393 s q → Prop

def frameWhereKids400 {s q} (frame : AuthoredBodyFrame393 s q) : List Request :=
  children q (frame.clauses.map LiteralWhereEntry.demand)

mutual
inductive GuardedFrameTree400 (source : FrameChoice400) (s : State) :
    Request → Dictionary → Type where
  | node {q ds} (frame : AuthoredBodyFrame393 s q) (guard : source s q frame) :
      GuardedFrameForest400 source s (frameWhereKids400 frame) ds →
      GuardedFrameTree400 source s q (.node frame.decl.id ds)

inductive GuardedFrameForest400 (source : FrameChoice400) (s : State) :
    List Request → List Dictionary → Type where
  | nil : GuardedFrameForest400 source s [] []
  | cons :
      GuardedFrameTree400 source s q d →
      GuardedFrameForest400 source s qs ds →
      GuardedFrameForest400 source s (q::qs) (d::ds)
end

mutual
/-- Exact paired tree: the old *source derivation* is the index, not
a new selected dictionary or a newly chosen equivalent frame. -/
inductive TypedFrameReceipts400 {source : FrameChoice400} {s : State} :
    {q : Request} → {d : Dictionary} → GuardedFrameTree400 source s q d → Type where
  | node {q ds} {frame : AuthoredBodyFrame393 s q} {guard : source s q frame}
      {sameKids : GuardedFrameForest400 source s (frameWhereKids400 frame) ds}
      (outputs : ∀ i : Fin q.demand.outputs.length, TreeOutput400 frame i) :
      TypedFrameForestReceipts400 sameKids →
      TypedFrameReceipts400 (.node frame guard sameKids)

inductive TypedFrameForestReceipts400 {source : FrameChoice400} {s : State} :
    {qs : List Request} → {ds : List Dictionary} → GuardedFrameForest400 source s qs ds → Type where
  | nil : TypedFrameForestReceipts400 .nil
  | cons :
      TypedFrameReceipts400 first →
      TypedFrameForestReceipts400 rest →
      TypedFrameForestReceipts400 (.cons first rest)
end

/-- Finite source inhabitation produces receipts directly from the
same frame, with the same guard at each child and no old literal
wire or old receipt input anywhere in the derivation. -/
theorem same_guarded_frame_tree_has_B6_receipts400 {source : FrameChoice400} {s q d}
    (tree : GuardedFrameTree400 source s q d)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (atlas : B6SymbolicAtlas398 s)
    (inputs : ∀ (q : Request) (f : AuthoredBodyFrame393 s q), source s q f →
      DeclaredOriginalOutputs400 s q ∧ FrameB6SourceInput400 f atlas) :
    Nonempty (TypedFrameReceipts400 tree) := by
  exact GuardedFrameTree400.rec
    (motive_1 := fun _ _ t => Nonempty (TypedFrameReceipts400 t))
    (motive_2 := fun _ _ ts => Nonempty (TypedFrameForestReceipts400 ts))
    (fun frame guard _ kids => by
      have allowed := inputs _ frame guard
      obtain ⟨event,frameEq,_,_⟩ :=
        exact_preoutput_frame_produces_tree_event400 frame checked allowed.1 atlas allowed.2
      cases event with
      | mk stored outputs =>
        change stored = frame at frameEq
        subst stored
        obtain ⟨children⟩ := kids
        exact ⟨.node outputs children⟩)
    ⟨.nil⟩
    (fun _ _ left right => by
      obtain ⟨a⟩ := left
      obtain ⟨b⟩ := right
      exact ⟨.cons a b⟩)
    tree

/-- Reuse the original rule's actual ordered derivation. This is not
a converse from the diagnostic key or finite dictionary to a frame. -/
theorem guarded_frame_tree_projects_exact_where400 {source : FrameChoice400} {s q d}
    (tree : GuardedFrameTree400 source s q d)
    {localRule : Request → Frontier Request → Prop}
    (projects : ∀ q (f : AuthoredBodyFrame393 s q), source s q f →
      localRule q (.selected f.decl.id (frameWhereKids400 f))) :
    Resolves localRule q (dictionaryTree d) := by
  exact GuardedFrameTree400.rec
    (motive_1 := fun q d _ => Resolves localRule q (dictionaryTree d))
    (motive_2 := fun qs ds _ => All₂ (Resolves localRule) qs (dictionaryForest ds))
    (fun f guard _ rest => by
      simpa only [dictionaryTree] using Resolves.selected (projects _ f guard) rest)
    (by rw [dictionaryForest]; exact .nil)
    (fun _ _ a b => by simpa only [dictionaryForest] using All₂.cons a b)
    tree

open CommonNominalFullCarrier (Ty)

def WrittenTreeAndPlanAgree400 {s q f i}
    (m : Model) (out : TreeOutput400 (s := s) (q := q) f i) : Prop :=
  match out.write with
  | .ordinary _ => True
  | .typed _ _ =>
    ∃ (plan : B6ValuePlan398 s false (GeneralDeclarationPatterns.normalize
          (GeneralDeclarativeOutputs320.bodyPattern out.body))) (value : Ty),
      out.originalPlan = some plan ∧
      out.actualEquation400 m = some (q.demand.outputs[i].target,value) ∧
      actualPlanValue400 m (f.slots out.body) plan = some value

mutual
def ActualMeaningOfSameTree400 (m : Model) {source s q d}
    {tree : GuardedFrameTree400 source s q d} : TypedFrameReceipts400 tree → Prop
  | .node outputs next =>
    (∀ i, WrittenTreeAndPlanAgree400 m (outputs i)) ∧ ActualMeaningOfSameForest400 m next

def ActualMeaningOfSameForest400 (m : Model) {source s qs ds}
    {forest : GuardedFrameForest400 source s qs ds} : TypedFrameForestReceipts400 forest → Prop
  | .nil => True
  | .cons first rest => ActualMeaningOfSameTree400 m first ∧ ActualMeaningOfSameForest400 m rest
end

/-- One and the same model for each selected node, every actual
associated output, and the complete original ordered where forest. -/
theorem paired_receipt_tree_has_same_actual_meaning400 {source s q d}
    {tree : GuardedFrameTree400 source s q d}
    (receipts : TypedFrameReceipts400 tree) (m : Model) :
    ActualMeaningOfSameTree400 m receipts := by
  exact TypedFrameReceipts400.rec
    (motive_1 := fun {_ _} _ out => ActualMeaningOfSameTree400 m out)
    (motive_2 := fun {_ _} _ out => ActualMeaningOfSameForest400 m out)
    (fun outputs kids rest => by
      rw [ActualMeaningOfSameTree400]
      exact ⟨fun i => typed_fixed_equation_matches_B6_value400 (outputs i) m,rest⟩)
    (by simp only [ActualMeaningOfSameForest400])
    (fun first rest left right => by
      rw [ActualMeaningOfSameForest400]
      exact ⟨left,right⟩)
    receipts

/-- No old wire and no occurrence is recovered by its declaration
key. The conclusion is for this very supplied guarded source proof;
it does not construct the all-state classifier or assert retention of
every equation by a solver. -/
theorem same_selected_source_B6_actual_equations400 {source : FrameChoice400} {s q d}
    (sourceTree : GuardedFrameTree400 source s q d)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    (atlas : B6SymbolicAtlas398 s)
    (inputs : ∀ (q : Request) (f : AuthoredBodyFrame393 s q), source s q f →
      DeclaredOriginalOutputs400 s q ∧ FrameB6SourceInput400 f atlas) :
    ∃ receipts : TypedFrameReceipts400 sourceTree,
      ∀ m : Model, ActualMeaningOfSameTree400 m receipts := by
  obtain ⟨receipts⟩ := same_guarded_frame_tree_has_B6_receipts400 sourceTree checked atlas inputs
  exact ⟨receipts,fun m => paired_receipt_tree_has_same_actual_meaning400 receipts m⟩

end Yulang.GeneralDeclarativeI65
