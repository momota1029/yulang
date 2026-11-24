import Yulang.GeneralDeclarativeI65B6MixedTree401

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (Dictionary)
open CommonNominalFullCarrier (Ty)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarations (Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDictionaryAssociatedProvenance (Body Supplies lookup lookup_exact)

/-- Pass the kinded RHS at the original request (including occurrence),
declaration ordinal, output ordinal and exact body. The annotation
does not supply the fixed output target or pick a different body. -/
structure B6OccurrenceAtlas401 (s : State) where
  read : (q : Request) → (declaration : Nat) → Fin q.demand.outputs.length →
    (b : Body) → Option (B6MixedRhs401 s false (normalize (bodyPattern b)))

def B6AtMixedFrame401 {s q} (atlas : B6OccurrenceAtlas401 s)
    (frame : AuthoredBodyFrame393 s q) : Prop :=
  ∀ (i : Fin q.demand.outputs.length) (body : Body),
    Supplies (authoredRegistry s.current).roles frame.decl q.demand.outputs[i].name body →
    ∃ plan : B6MixedRhs401 s false (normalize (bodyPattern body)),
      atlas.read q frame.ordinal i body = some plan ∧
      B6UsesFit398 s (frame.slots body) (mixedRhsNeeds401 plan)

structure MixedOutput401 {s q} (atlas : B6OccurrenceAtlas401 s)
    (frame : AuthoredBodyFrame393 s q) (i : Fin q.demand.outputs.length) where
  body : Body
  supplied : Supplies (authoredRegistry s.current).roles frame.decl q.demand.outputs[i].name body
  plan : B6MixedRhs401 s false (normalize (bodyPattern body))
  originalAnnotation : atlas.read q frame.ordinal i body = some plan
  ready : B6UsesFit398 s (frame.slots body) (mixedRhsNeeds401 plan)
  rhs : RetainedTree401 s (frame.slots body) false (normalize (bodyPattern body))
  built : substituteMixedRhs401 (instantiateMixedSlot401 (s := s) (frame.slots body)) plan = some rhs

structure MixedReceipt401 {s : State} where
  occurrence : List Nat
  ordinal : Nat
  requested : GeneralSourceState.Output
  body : Body
  slots : Nat → Option Capture
  rhs : RetainedTree401 s slots false (normalize (bodyPattern body))

def MixedOutput401.receipt {s q atlas frame i}
    (output : MixedOutput401 (s := s) (q := q) atlas frame i) : MixedReceipt401 (s := s) :=
  ⟨q.occurrence,i,q.demand.outputs[i],output.body,frame.slots output.body,output.rhs⟩

def MixedReceipt401.actualEquation {s} (r : MixedReceipt401 (s := s)) (m : Model) :
    Option (Nat × Ty) :=
  (evaluateMixedRhs401 (retainedRead401 m) r.rhs).map fun ty => (r.requested.target,ty)

/-- Body selection is the checked original authored lookup, not a
value chosen by the B6 atlas. All three addresses remain literal and
the whole type continues at the requested target. -/
theorem mixed_write_is_original_lookup401 {s q atlas frame i}
    (out : MixedOutput401 (s := s) (q := q) atlas frame i)
    (checked : Checked (authoredRegistry s.current)) :
    out.receipt.occurrence = q.occurrence ∧ out.receipt.ordinal = i.val ∧
    q.demand.outputs[i.val]? = some out.receipt.requested ∧
    lookup (authoredRegistry s.current).roles frame.decl out.receipt.requested.name = some out.body := by
  have checkedRow := checked.2 frame.decl (List.mem_of_getElem? frame.authored)
  exact ⟨rfl,rfl,List.getElem?_eq_getElem i.isLt,
    (lookup_exact _ _ checkedRow.identified.2.2.1 _ _).mpr out.supplied⟩

theorem mixed_write_same_model_fixed_target401 {s q atlas frame i}
    (out : MixedOutput401 (s := s) (q := q) atlas frame i) (m : Model) :
    ∃ ty, out.receipt.actualEquation m = some (q.demand.outputs[i].target,ty) ∧
      evaluateMixedRhs401 (sourceRead401 m (frame.slots out.body)) out.plan = some ty := by
  obtain ⟨ty,built,body⟩ := exact_mixed_source_and_retained_values401 out.ready out.built m
  exact ⟨ty,by simp [MixedReceipt401.actualEquation,MixedOutput401.receipt,built],body⟩

theorem original_frame_emits_exact_mixed_output401 {s q}
    (frame : AuthoredBodyFrame393 s q) (checked : Checked (authoredRegistry s.current))
    (declared : DeclaredOriginalOutputs400 s q) (atlas : B6OccurrenceAtlas401 s)
    (supplied : B6AtMixedFrame401 atlas frame) (i : Fin q.demand.outputs.length) :
    Nonempty (MixedOutput401 atlas frame i) := by
  have rule := checked.2 frame.decl (List.mem_of_getElem? frame.authored)
  have actual := (visible_exact s q frame.decl).mp frame.inScope |>.2
  obtain ⟨b,inBody⟩ := GeneralDictionaryAssociatedProvenance.declared_covered
    (authoredRegistry s.current).roles frame.decl rule.signature
    q.demand.outputs[i].name (actual ▸ declared i)
  obtain ⟨plan,inAtlas,fit⟩ := supplied i b inBody
  obtain ⟨tree,made⟩ := supplied_mixed_tree_substitution_succeeds401 (frame.slots b) plan fit
  exact ⟨⟨b,inBody,plan,inAtlas,fit,tree,made⟩⟩

structure MixedLocalOutputs401 {s q}
    (atlas : B6OccurrenceAtlas401 s) (frame : AuthoredBodyFrame393 s q) where
  each : ∀ i : Fin q.demand.outputs.length, MixedOutput401 atlas frame i

def MixedLocalOutputs401.written {s q atlas frame}
    (out : MixedLocalOutputs401 (s := s) (q := q) atlas frame) : List (MixedReceipt401 (s := s)) :=
  List.ofFn fun i => (out.each i).receipt

theorem ordered_mixed_writes_at_actual_origin401 {s q atlas frame}
    (out : MixedLocalOutputs401 (s := s) (q := q) atlas frame) (i : Fin q.demand.outputs.length) :
    out.written[i.val]? = some (out.each i).receipt ∧ out.written.length = q.demand.outputs.length := by
  simp [MixedLocalOutputs401.written]

/- Independent role selection is an input, so this is exact output
production for the same guards rather than a new rule for acceptance. -/
mutual
inductive MixedReceiptsAtTree401 {source : FrameChoice400} {s : State}
    (atlas : B6OccurrenceAtlas401 s) :
    {q : Request} → {d : Dictionary} → GuardedFrameTree400 source s q d → Type where
  | node {q ds} {f : AuthoredBodyFrame393 s q} {guard : source s q f}
      {sameKids : GuardedFrameForest400 source s (frameWhereKids400 f) ds} :
      MixedLocalOutputs401 atlas f → MixedReceiptsAtForest401 atlas sameKids →
      MixedReceiptsAtTree401 atlas (.node f guard sameKids)

inductive MixedReceiptsAtForest401 {source : FrameChoice400} {s : State}
    (atlas : B6OccurrenceAtlas401 s) :
    {qs : List Request} → {ds : List Dictionary} → GuardedFrameForest400 source s qs ds → Type where
  | nil : MixedReceiptsAtForest401 atlas .nil
  | cons : MixedReceiptsAtTree401 atlas first → MixedReceiptsAtForest401 atlas rest →
      MixedReceiptsAtForest401 atlas (.cons first rest)
end

theorem guarded_source_produces_exact_mixed_receipts401 {source : FrameChoice400} {s q d}
    (tree : GuardedFrameTree400 source s q d) (checked : Checked (authoredRegistry s.current))
    (atlas : B6OccurrenceAtlas401 s)
    (inputs : ∀ q (f : AuthoredBodyFrame393 s q), source s q f →
      DeclaredOriginalOutputs400 s q ∧ B6AtMixedFrame401 atlas f) :
    Nonempty (MixedReceiptsAtTree401 atlas tree) := by
  classical
  exact GuardedFrameTree400.rec
    (motive_1 := fun _ _ t => Nonempty (MixedReceiptsAtTree401 atlas t))
    (motive_2 := fun _ _ ts => Nonempty (MixedReceiptsAtForest401 atlas ts))
    (fun f guard _ ih => by
      obtain ⟨declared,typed⟩ := inputs _ f guard
      obtain ⟨kids⟩ := ih
      exact ⟨.node ⟨fun i => Classical.choice (original_frame_emits_exact_mixed_output401
        f checked declared atlas typed i)⟩ kids⟩)
    ⟨.nil⟩
    (fun _ _ a b => by
      obtain ⟨first⟩ := a
      obtain ⟨rest⟩ := b
      exact ⟨.cons first rest⟩)
    tree


/-- Exact sourced equality for every original output at this node.
This associates the interpreted source type to the fixed target; it
does not assert solver retention of that equality in the model. -/
def LocalMixedMeaning401 {s q atlas frame}
    (m : Model) (out : MixedLocalOutputs401 (s := s) (q := q) atlas frame) : Prop :=
  ∀ i : Fin q.demand.outputs.length,
    let result := out.each i
    out.written[i.val]? = some result.receipt ∧
    result.receipt.occurrence = q.occurrence ∧ result.receipt.ordinal = i.val ∧
    lookup (authoredRegistry s.current).roles frame.decl q.demand.outputs[i].name = some result.body ∧
    atlas.read q frame.ordinal i result.body = some result.plan ∧
    ∃ ty, result.receipt.actualEquation m = some (q.demand.outputs[i].target,ty) ∧
      evaluateMixedRhs401 (sourceRead401 m (frame.slots result.body)) result.plan = some ty

theorem original_mixed_local_meaning401 {s q atlas frame}
    (m : Model) (out : MixedLocalOutputs401 (s := s) (q := q) atlas frame)
    (checked : Checked (authoredRegistry s.current)) :
    LocalMixedMeaning401 m out := by
  intro i
  have src := mixed_write_is_original_lookup401 (out.each i) checked
  exact ⟨(ordered_mixed_writes_at_actual_origin401 out i).1,src.1,src.2.1,src.2.2.2,
    (out.each i).originalAnnotation,mixed_write_same_model_fixed_target401 (out.each i) m⟩

mutual
def SameMixedTreeMeaning401 (m : Model) {source s q d atlas}
    {tree : GuardedFrameTree400 source s q d} : MixedReceiptsAtTree401 atlas tree → Prop
  | .node out rest => LocalMixedMeaning401 m out ∧ SameMixedForestMeaning401 m rest

def SameMixedForestMeaning401 (m : Model) {source s qs ds atlas}
    {forest : GuardedFrameForest400 source s qs ds} : MixedReceiptsAtForest401 atlas forest → Prop
  | .nil => True
  | .cons a b => SameMixedTreeMeaning401 m a ∧ SameMixedForestMeaning401 m b
end

theorem guarded_receipts_have_same_mixed_meaning401 {source s q d atlas}
    {tree : GuardedFrameTree400 source s q d} (receipts : MixedReceiptsAtTree401 atlas tree)
    (checked : Checked (authoredRegistry s.current)) (m : Model) :
    SameMixedTreeMeaning401 m receipts := by
  exact MixedReceiptsAtTree401.rec
    (motive_1 := fun {_ _} _ out => SameMixedTreeMeaning401 m out)
    (motive_2 := fun {_ _} _ out => SameMixedForestMeaning401 m out)
    (fun out _ rest => by
      rw [SameMixedTreeMeaning401]
      exact ⟨original_mixed_local_meaning401 m out checked,rest⟩)
    (by simp only [SameMixedForestMeaning401])
    (fun a b ha hb => by
      rw [SameMixedForestMeaning401]
      exact ⟨ha,hb⟩)
    receipts

/-- The proof object is built once from source and the B6 atlas. The
claim then holds in every one given model at every node and ordered
output, including mixed declared, primitive and structural RHS trees.
No old flattened C386 wire or early selection from a model is used. -/
theorem source_tree_retains_exact_original_mixed_outputs401 {source : FrameChoice400} {s q d}
    (tree : GuardedFrameTree400 source s q d) (checked : Checked (authoredRegistry s.current))
    (atlas : B6OccurrenceAtlas401 s)
    (inputs : ∀ q (f : AuthoredBodyFrame393 s q), source s q f →
      DeclaredOriginalOutputs400 s q ∧ B6AtMixedFrame401 atlas f) :
    ∃ receipts : MixedReceiptsAtTree401 atlas tree, ∀ m, SameMixedTreeMeaning401 m receipts := by
  obtain ⟨receipts⟩ := guarded_source_produces_exact_mixed_receipts401 tree checked atlas inputs
  exact ⟨receipts,fun m => guarded_receipts_have_same_mixed_meaning401 receipts checked m⟩

end Yulang.GeneralDeclarativeI65
