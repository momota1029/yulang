import Yulang.GeneralDeclarativeI65ActualJoinFrame402
import Yulang.GeneralDeclarativeI65ActualJoinTrace381
import Yulang.GeneralDeclarativeWitnessRootDeclared357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open CommonRoleOutermostResolver (All₂ Tree Dictionary Result Summarizes Combine classification_exact)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

mutual
/--
Frame data indexed by the exact received join trace. The event and
the full ordered where source trace are the indices. In particular,
the relation cannot replay a different event with an equal key.
-/
inductive JoinFramesOnTrace402 {s : State} :
    {q : Request} → {t : Tree} → SourceEventTrace381 (ActualWrittenJoin381 s) q t → Dictionary → Type where
  | node (event : WrittenJoinEvent381 s) (frame : OriginalJoinFrame402 event)
      {kids : SourceEventForest381 (ActualWrittenJoin381 s) (children event.request event.demands) ts} :
      JoinFramesOnForest402 kids ds →
      JoinFramesOnTrace402 (.selected event (.authored event) kids) (.node event.row.id ds)

inductive JoinFramesOnForest402 {s : State} :
    {qs : List Request} → {ts : List Tree} →
    SourceEventForest381 (ActualWrittenJoin381 s) qs ts → List Dictionary → Type where
  | nil : JoinFramesOnForest402 .nil []
  | cons : JoinFramesOnTrace402 a d → JoinFramesOnForest402 later ds →
      JoinFramesOnForest402 (.cons a later) (d::ds)
end

theorem actual_join_trace_produces_its_original_frames402 {s q t}
    (trace : SourceEventTrace381 (ActualWrittenJoin381 s) q t) :
    ∃ d : Dictionary, Nonempty (JoinFramesOnTrace402 trace d) ∧ Summarizes t (.selected d) := by
  exact SourceEventTrace381.rec
    (motive_1 := fun _ t src => ∃ d,
      Nonempty (JoinFramesOnTrace402 src d) ∧ Summarizes t (.selected d))
    (motive_2 := fun _ ts src => ∃ ds,
      Nonempty (JoinFramesOnForest402 src ds) ∧ All₂ Summarizes ts (ds.map Result.selected))
    (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible)
    (fun _ impossible => nomatch impossible)
    (fun event chosen _ more => by
      cases chosen
      obtain ⟨f⟩ := source_selected_join_has_preoutput402 event
      obtain ⟨ds,⟨rest⟩,summary⟩ := more
      exact ⟨_,⟨.node event f rest⟩,.selected summary (.selected rfl)⟩)
    ⟨[],⟨.nil⟩,.nil⟩
    (fun _ _ a b => by
      obtain ⟨_,⟨first⟩,summary⟩ := a
      obtain ⟨_,⟨rest⟩,children⟩ := b
      exact ⟨_,⟨.cons first rest⟩,.cons summary children⟩)
    trace

theorem frame_tree_at_same_reported_join_dictionary402 {s q t d}
    (trace : SourceEventTrace381 (ActualWrittenJoin381 s) q t) (reported : Summarizes t (.selected d)) :
    Nonempty (JoinFramesOnTrace402 trace d) := by
  obtain ⟨found,picked,summary⟩ := actual_join_trace_produces_its_original_frames402 trace
  have a := (classification_exact t (.selected found)).mpr summary
  have b := (classification_exact t (.selected d)).mpr reported
  have same : found = d := Result.selected.inj (a.symm.trans b)
  exact same ▸ picked

def ActualJoinFrameGuard402 : FrameChoice400 :=
  fun s q frame =>
    ∃ (event : WrittenJoinEvent381 s) (same : event.request = q) (root : OriginalJoinFrame402 event),
      cast (congrArg (AuthoredBodyFrame393 s) same) root.frame = frame

mutual
def JoinFramesOnTrace402.toGuarded {s q t d}
    {trace : SourceEventTrace381 (ActualWrittenJoin381 s) q t}
    (kept : JoinFramesOnTrace402 trace d) : GuardedFrameTree400 ActualJoinFrameGuard402 s q d :=
  match kept with
  | .node e original below =>
    let prepared := original.frame
    let children := below.toGuarded
    .node prepared ⟨e,rfl,original,rfl⟩
      (cast (congrArg (fun qs => GuardedFrameForest400 ActualJoinFrameGuard402 s qs _)
        (actual_join_frame_keeps_exact_where402 original).2.2.symm) children)

def JoinFramesOnForest402.toGuarded {s qs ts ds}
    {trace : SourceEventForest381 (ActualWrittenJoin381 s) qs ts}
    (kept : JoinFramesOnForest402 trace ds) : GuardedFrameForest400 ActualJoinFrameGuard402 s qs ds :=
  match kept with
  | .nil => .nil
  | .cons a b => .cons a.toGuarded b.toGuarded
end

open GeneralDeclarations (Checked)
open GeneralDeclarativeWitnessRootDeclared357 (written_root_declared)

/-- The root role signature is available from the actual source head
and original successful authored body; no second declaration/output
predicate has to be given to the new tree receiver. -/
theorem actual_join_has_original_signature402 {s : State}
    (e : WrittenJoinEvent381 s) (checked : Checked (authoredRegistry s.current)) :
    AuthoredRequestSignature401 s e.request := by
  have visible : e.row ∈ visible s e.request := by
    rw [written_join_original_visible_order381]; exact List.mem_cons_self
  obtain ⟨active,role⟩ := (visible_exact s e.request e.row).mp visible
  have legal := checked.2 e.row active
  constructor
  · calc
      e.request.demand.arguments.length = e.row.head.length :=
        observed_preoutput_demand_head_lengths399 (SourceHead.joined e.authored.head)
      _ = ((authoredRegistry s.current).roles e.row.role).arity := legal.signature.1
      _ = ((authoredRegistry s.current).roles e.request.demand.role).arity := by rw [role]
  · intro i
    exact written_root_declared e.authored.body legal.signature legal.identified.2.2.1 role
      e.request.demand.outputs[i] (List.getElem_mem i.isLt)

private theorem root_from_original_join_guard402 {s q d}
    (tree : GuardedFrameTree400 ActualJoinFrameGuard402 s q d) (checked : Checked (authoredRegistry s.current)) :
    AuthoredRequestSignature401 s q := by
  cases tree with
  | node f guard _ =>
    obtain ⟨event,root,_,_⟩ := guard
    exact root ▸ actual_join_has_original_signature402 event checked

/-- A genuine existing selected join trace itself provides the frame
tree. Only the B6 annotations are now external input, keyed by the
actual request, original offset, output ordinal and provider. I-71
does not require or carry a flattened C386 write to this receiver.
This is the existing covariant-join case, not all Classifies cases. -/
theorem actual_join_trace_supplies_modern_typed_outputs402 {s q t d}
    (trace : SourceEventTrace381 (ActualWrittenJoin381 s) q t) (reported : Summarizes t (.selected d))
    (checked : Checked (authoredRegistry s.current)) (atlas : B6OccurrenceAtlas401 s)
    (typed : ∀ (e : WrittenJoinEvent381 s) (f : OriginalJoinFrame402 e),
      NamedInputAtStoredHead401 atlas f.frame) :
    ∃ frames : JoinFramesOnTrace402 trace d,
      ∃ receipts : NamedReceiptsAtTree401 atlas frames.toGuarded,
        ∀ m : Model, ExactNamedTreeMeaning401 m receipts := by
  obtain ⟨frames⟩ := frame_tree_at_same_reported_join_dictionary402 trace reported
  refine ⟨frames,?_⟩
  apply original_guarded_tree_produces_mixed_source_values401 frames.toGuarded checked atlas
  · intro root f good
    obtain ⟨e,eq,original,provenance⟩ := good
    subst root
    cases provenance
    exact typed e original
  · exact root_from_original_join_guard402 frames.toGuarded checked


/-- In the actual C357 classification, a written native join at the
root can be inverted even when its children are not joins. The result
keeps the genuine rule's exact local where requests and diagnostic
subforest. It does not infer a child frame from its diagnostic key. -/
theorem selected_C357_root_supplies_exact_join_frame402 {s d}
    (scope : WrittenJoinHeadScope381 s)
    (selected : CommonRoleOutermostResolver.Classify
      (GeneralDeclarativeWitnessClassifyVariance357.Rule s.current) scope.request.demand (.selected d)) :
    ∃ (e : WrittenJoinEvent381 s) (frame : OriginalJoinFrame402 e) (ts : List Tree),
      e.request = scope.request ∧ e.row = scope.row ∧
      frameWhereKids400 frame.frame = children e.request e.demands ∧
      All₂ (CommonRoleOutermostResolver.Resolves
        (GeneralDeclarativeWitnessClassifyVariance357.Rule s.current)) e.demands ts ∧
      Summarizes (.selected e.row.id ts) (.selected d) := by
  obtain ⟨tree,actual,summary⟩ := selected
  cases actual with
  | pending _ => cases summary
  | ambiguous _ => cases summary
  | rejected _ => cases summary
  | selected top below =>
    obtain ⟨ev,root,decl,same,rule⟩ := invert_actual_C357_at_written_join381 scope top
    injection same with key demand
    obtain ⟨f⟩ := source_selected_join_has_preoutput402 ev
    exact ⟨ev,f,_,root,decl,(actual_join_frame_keeps_exact_where402 f).2.2,
      demand ▸ below,key ▸ summary⟩

theorem actual_C357_scope_to_exact_mixed_sources402 {s q t d}
    (actualTrace : ActualC357JoinTrace381 s q t) (reported : Summarizes t (.selected d))
    (checked : Checked (authoredRegistry s.current)) (atlas : B6OccurrenceAtlas401 s)
    (typed : ∀ (e : WrittenJoinEvent381 s) (f : OriginalJoinFrame402 e),
      NamedInputAtStoredHead401 atlas f.frame) :
    ∃ (trace : SourceEventTrace381 (ActualWrittenJoin381 s) q t) (frames : JoinFramesOnTrace402 trace d),
      ∃ receipts : NamedReceiptsAtTree401 atlas frames.toGuarded,
        ∀ m : Model, ExactNamedTreeMeaning401 m receipts := by
  obtain ⟨trace⟩ := actual_C357_join_trace_extracts_events381 actualTrace
  obtain ⟨frames,receipts,meaning⟩ := actual_join_trace_supplies_modern_typed_outputs402
    trace reported checked atlas typed
  exact ⟨trace,frames,receipts,meaning⟩

end Yulang.GeneralDeclarativeI65
