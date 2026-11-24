import Yulang.GeneralDeclarativeI65WrittenJoinEvents381
import Yulang.GeneralDeclarativeI65MixedQualification401
import Yulang.GeneralDeclarativeI65Compiler367

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry context point pointSpans)
open GeneralDeclarativeWitnessCompiler350 (Context Finished execute preparation portNames placed initial)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeClauseBatch327 (Port)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarations (Checked Declaration Equation)
open CommonRoleOutermostResolver (Dictionary)

abbrev Ordinary402 := GeneralDeclarativeHead320.State

/-- Only pre-output data sealed by the very same compilation call.
This is not a certificate about fixed output retention, nor a new
candidate acceptance rule. -/
structure ExecutedPrefix402 (c : Context) (f : Finished) where
  beforeWhere : Ordinary402
  ports : List Port
  ran : preparation c = some (beforeWhere,ports)
  kids : f.kids = GeneralDeclarativeEmissionForest322.children c.decl (portNames c ports) (placed c ports)

/-- Invert the existing successful body, never replace its allocator by
one chosen from the same target or another matching declaration. The
old fixed batch is inspected only to invert the already-existing run. -/
theorem preoutput_prefix_of_real_execute402 {c : Context} {f : Finished}
    (run : execute c = some f) : Nonempty (ExecutedPrefix402 c f) := by
  unfold execute at run
  cases prep : preparation c with
  | none => simp [prep] at run
  | some packed =>
    rcases packed with ⟨earlier,ports⟩
    cases localRows : GeneralDeclarativeWitnessCompiler350.whereBatch c ports with
    | none => simp [prep,localRows] at run
    | some wh =>
      cases fixed : GeneralDeclarativeWitnessCompiler350.fixedBatch c ports with
      | none => simp [prep,localRows,fixed] at run
      | some outputs =>
        have eq : (⟨appendFacts earlier wh,outputs,
          GeneralDeclarativeEmissionForest322.children c.decl (portNames c ports) (placed c ports)⟩ : Finished) = f := by
          simpa [prep,localRows,fixed] using run
        cases eq
        exact ⟨⟨earlier,ports,prep,rfl⟩⟩

def actualJoinContext402 {s : State} (event : WrittenJoinEvent381 s) : Context :=
  let original := event.authored.body
  context s.current event.request.demand event.row original.named
    (pointSpans event.authored.head.firstBinder event.authored.head.lastBinder event.authored.head.actualValue)
    original.keep original.fallback original.targets

theorem actual_join_at_first_visible_ordinal402 {s : State} (event : WrittenJoinEvent381 s) :
    (visible s event.request)[0]? = some event.row := by
  rw [written_join_original_visible_order381]
  rfl

structure OriginalJoinFrame402 {s : State} (event : WrittenJoinEvent381 s) where
  offset : Nat
  original : (authoredRegistry s.current).declarations[offset]? = some event.row
  fromFilter : unfilterOrdinal395 (fun row : Declaration => row.role == event.request.demand.role)
    (authoredRegistry s.current).declarations 0 = some offset
  prep : ExecutedPrefix402 (actualJoinContext402 event) event.authored.body.finished

theorem source_selected_join_has_preoutput402 {s : State} (event : WrittenJoinEvent381 s) :
    Nonempty (OriginalJoinFrame402 event) := by
  obtain ⟨offset,fromFilter,original⟩ := unfilterOrdinal395_exact _ _ 0 (actual_join_at_first_visible_ordinal402 event)
  obtain ⟨prep⟩ := preoutput_prefix_of_real_execute402 event.authored.body.run
  exact ⟨⟨offset,original,fromFilter,prep⟩⟩

def OriginalJoinFrame402.frame {s : State} {event : WrittenJoinEvent381 s} (f : OriginalJoinFrame402 event) :
    AuthoredBodyFrame393 s event.request :=
  frameAtSource395 (by rw [written_join_original_visible_order381]; exact List.mem_cons_self)
    f.offset f.original (placed (actualJoinContext402 event) f.prep.ports)
    (initial (actualJoinContext402 event)).captures

theorem actual_join_frame_keeps_exact_where402 {s : State}
    {e : WrittenJoinEvent381 s} (f : OriginalJoinFrame402 e) :
    f.frame.decl = e.row ∧ f.frame.ordinal = f.offset ∧
    frameWhereKids400 f.frame = children e.request e.demands := by
  refine ⟨rfl,rfl,?_⟩
  have literal : f.frame.clauses.map LiteralWhereEntry.demand =
      GeneralDeclarativeEmissionForest322.children (actualJoinContext402 e).decl
        (portNames (actualJoinContext402 e) f.prep.ports) (placed (actualJoinContext402 e) f.prep.ports) := by
    unfold OriginalJoinFrame402.frame AuthoredBodyFrame393.clauses GeneralDeclarativeEmissionForest322.children
    rw [List.map_map]
    rfl
  rw [frameWhereKids400,literal,← f.prep.kids,e.authored.body.children]

/-- The source's same two lexical binders are fed from the actual
merged center. C350 may introduce new endpoint names; equality of
the full triples is deliberately not claimed. -/
theorem actual_join_frame_keeps_both_merged_centers402 {s : State}
    {e : WrittenJoinEvent381 s} (f : OriginalJoinFrame402 e)
    (checked : Checked (authoredRegistry s.current)) :
    (f.frame.names.input e.authored.head.firstBinder).center = e.authored.head.actualValue ∧
    (f.frame.names.input e.authored.head.lastBinder).center = e.authored.head.actualValue := by
  have valid := checked.2 e.row (List.mem_of_getElem? f.original)
  have names := joined_input_names_exact399 e.authored.head
  have notOutput : ∀ n ∈ e.row.inputNames, n ∉ e.row.outputNames := by
    intro n input output
    exact valid.outputOnly.1 n output
      (GeneralPatternVariableProvenance.normalize_args_variables e.row.head input)
  have first : e.authored.head.firstBinder ∈ e.row.inputNames := by rw [names]; exact List.mem_cons_self
  have last : e.authored.head.lastBinder ∈ e.row.inputNames := by rw [names]; simp
  have foundFirst : ((actualJoinContext402 e).spans.find?
      (fun item => item.1 == e.authored.head.firstBinder)).map Prod.snd =
        some (point e.authored.head.actualValue) := by
    simp [actualJoinContext402,context,pointSpans]
  have foundLast : ((actualJoinContext402 e).spans.find?
      (fun item => item.1 == e.authored.head.lastBinder)).map Prod.snd =
        some (point e.authored.head.actualValue) := by
    simp [actualJoinContext402,context,pointSpans,e.authored.head.different]
  exact ⟨actual_port_center (ports := f.prep.ports) foundFirst (notOutput _ first),
    actual_port_center (ports := f.prep.ports) foundLast (notOutput _ last)⟩

theorem same_actual_join_frame_is_determined402 {s : State} {e : WrittenJoinEvent381 s}
    (first last : OriginalJoinFrame402 e) :
    first.frame = last.frame := by
  have offset := Option.some.inj (first.fromFilter.symm.trans last.fromFilter)
  have prep := Option.some.inj (first.prep.ran.symm.trans last.prep.ran)
  have ports : first.prep.ports = last.prep.ports := congrArg Prod.snd prep
  unfold OriginalJoinFrame402.frame frameAtSource395
  simp only [offset,ports]

end Yulang.GeneralDeclarativeI65
