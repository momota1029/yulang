import Yulang.GeneralDeclarativeI65I74StructuralWhereRead427
import Yulang.GeneralDeclarativeI65I72FixedGoal402

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry point)
open GeneralDeclarativeHead320 (Equation byMode)
open GeneralDeclarativeSubstitution320 (logical logicals)
open CommonRoleOutermostResolver (Dictionary)
open I72 (Event SourcePrimitives SourceTrace WhereForest DictionaryEvidence LocalMeaning FixedTargets RootCycle)
open GeneralDeclarativeEmissionForest322 (Placement)

private def noPlacement427 : Placement :=
  ⟨fun _ _ => point 0,fun _ _ => 0⟩

/-- A supported concrete positive leaf for the original compound where
child. This narrow independent packet is not the R15 rule or public
checker. It retains the exact witness of the original parent/child
position and the actual source head of the visible child declaration. -/
structure ClosedChild427 {s q f k}
    (a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0) where
  decl : Declaration
  ordinal : Nat
  authored : (authoredRegistry s.current).declarations[ordinal]? = some decl
  only : visible s a.child = [decl]
  checked : DeclarationChecked (authoredRegistry s.current).constructors
    (authoredRegistry s.current).roles decl
  binder : Nat
  empty : Nat
  written : decl.head = [writtenRecord427 a.label binder empty]
  compiled : translateWhere427 s (writtenRecord427 a.label binder empty) =
    some (recordCode427 a.label binder)
  arguments : a.child.demand.arguments = [point a.name]
  noOutputs : a.child.demand.outputs = []
  noWhere : decl.requirements = []

def ClosedChild427.capture {s q f k} {a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0}
    (d : ClosedChild427 a) (n : Nat) : Capture :=
  if n = d.binder then point (f.names.input a.binder).center else point 0

def ClosedChild427.sourceHead {s q f k} {a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0}
    (d : ClosedChild427 a) : SourceHead s a.child d.decl := by
  refine .ordered d.capture ?_
  rw [d.arguments,d.written]
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,recordCode427 a.label d.binder,d.compiled,.direct (.whole ?_)⟩) .nil
  have actual := List.mem_of_getElem? a.retained
  simpa [ClosedChild427.capture,writtenRow427,recordCode427,logical,logicals,point,byMode] using actual

def ClosedChild427.frame {s q f k} {a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0}
    (d : ClosedChild427 a) : AuthoredBodyFrame393 s a.child :=
  ⟨d.ordinal,d.decl,d.authored,by simp [d.only],noPlacement427,d.capture⟩

def ClosedChild427.event {s q f k} {a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0}
    {atlas : B6OccurrenceAtlas401 s} (d : ClosedChild427 a) : Event ⟨s,atlas⟩ a.child :=
  ⟨d.frame,d.sourceHead,fun i => by
    have impossible := i.isLt
    simp [d.noOutputs] at impossible⟩

theorem closed_child_no_where427 {s q f k} {a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0}
    {atlas : B6OccurrenceAtlas401 s} (d : ClosedChild427 a) :
    (d.event (atlas:=atlas)).kids = [] := by
  simp [I72.Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,ClosedChild427.event,
    ClosedChild427.frame,d.noWhere,children]

theorem original_compound_child_has_positive_same_model_dictionary427 {s q f k}
    {a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0} {atlas : B6OccurrenceAtlas401 s}
    (d : ClosedChild427 a) (m : Model) (fit : Fits s m) :
    DictionaryEvidence ⟨s,atlas⟩ m a.child (.node d.decl.id []) := by
  have noKids := closed_child_no_where427 (atlas:=atlas) d
  have localFact : LocalMeaning m (d.event (atlas:=atlas)) := by
    refine ⟨source_head_sound d.sourceHead m fit,?_⟩
    intro i
    have impossible := i.isLt
    simp [d.noOutputs] at impossible
  have retained : FixedTargets m (d.event (atlas:=atlas)) := by
    intro i
    have impossible := i.isLt
    simp [d.noOutputs] at impossible
  exact .node (d.event (atlas:=atlas)) localFact retained (noKids.symm ▸ .nil)

/-- Other rules can use the exact positive child proof at the original
request (not a regenerated equivalent demand). The rule membership and
raw-root guard are kept explicit in this reusable transport. -/
theorem original_compound_child_has_selected_trace427 {s q f k}
    {a : OriginalRecordArgument427 (s:=s) (q:=q) f k 0} {atlas : B6OccurrenceAtlas401 s}
    {R : SourcePrimitives} (d : ClosedChild427 a)
    (picked : R.elected ⟨s,atlas⟩ a.child (d.event (atlas:=atlas)) [])
    (safe : ¬ RootCycle ⟨s,atlas⟩ a.child) :
    Nonempty (SourceTrace R ⟨s,atlas⟩ a.child (.selected d.decl.id []) (some d.event)) := by
  have noKids := closed_child_no_where427 (atlas:=atlas) d
  exact ⟨.selected d.event safe picked .nil (noKids.symm ▸ .nil)⟩

end Yulang.GeneralDeclarativeI65.StructuralWhere427
