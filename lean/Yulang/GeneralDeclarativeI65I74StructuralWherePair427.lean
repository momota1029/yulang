import Yulang.GeneralDeclarativeI65I74StructuralWhereRivalRead427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427

theorem one_structural_where_has_exact_original_child427 {s q f}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f 0 0)
    (single : f.decl.requirements.length = 1) :
    frameWhereKids400 f = [a.child] := by
  have atZero := structural_where_keeps_original_child_at_ordinal427 a
  have one : (frameWhereKids400 f).length = 1 := by
    simpa [frameWhereKids400,children,AuthoredBodyFrame393.clauses] using single
  generalize data : frameWhereKids400 f = xs at atZero one ⊢
  cases xs with
  | nil => simp at one
  | cons head tail =>
    have ends : tail = [] := List.length_eq_zero_iff.mp (by simpa using one)
    subst tail
    exact congrArg (fun b => [b]) (Option.some.inj atZero)

private theorem event_meaning427 {s : State} {q : Request} {f : AuthoredBodyFrame393 s q}
    {atlas : B6OccurrenceAtlas401 s} {h : SourceHead s q f.decl}
    (nothing : q.demand.outputs = []) (m : Model) (fit : Fits s m) :
    I72.LocalMeaning m (originalNoOutputEvent427 atlas f h nothing) ∧
    I72.FixedTargets m (originalNoOutputEvent427 atlas f h nothing) := by
  refine ⟨⟨source_head_sound h m fit,?_⟩,?_⟩ <;>
    (intro i; exact Fin.elim0 (Fin.cast (congrArg List.length nothing) i))

/-- Both positive nodes use the original named source head and a
single actual structural child. The visible-set proof may be supplied
separately by the real two-candidate rival cut. Installation into
canonical classification/report dispatch is deliberately not implied. -/
theorem same_state_structural_where_pair_has_fixed_dictionary427 {s q f atlas}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f 0 0)
    (childFrame : AuthoredBodyFrame393 s a.child)
    (parent : SourceHead s q f.decl)
    (child : SourceHead s a.child childFrame.decl)
    (each : f.decl.requirements.length = 1)
    (zeroParent : q.demand.outputs = [])
    (zeroChild : a.child.demand.outputs = [])
    (closed : childFrame.decl.requirements = [])
    (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidence ⟨s,atlas⟩ m q (.node f.decl.id [.node childFrame.decl.id []]) := by
  let er := originalNoOutputEvent427 atlas f parent zeroParent
  let ec := originalNoOutputEvent427 atlas childFrame child zeroChild
  have erKids : er.kids = [a.child] := one_structural_where_has_exact_original_child427 a each
  have ecKids : ec.kids = [] := by
    simp [ec,originalNoOutputEvent427,I72.Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,closed]
  have ⟨rootMeaning,rootTargets⟩ := event_meaning427 (f:=f) (atlas:=atlas) (h:=parent) zeroParent m fit
  have ⟨childMeaning,childTargets⟩ := event_meaning427 (f:=childFrame) (atlas:=atlas) (h:=child) zeroChild m fit
  have childTree : I72.DictionaryEvidence ⟨s,atlas⟩ m a.child (.node childFrame.decl.id []) := by
    refine .node ec childMeaning childTargets ?_
    rw [ecKids]
    exact .nil
  refine .node er rootMeaning rootTargets ?_
  rw [erKids]
  exact .cons childTree .nil

end Yulang.GeneralDeclarativeI65.StructuralWhere427
