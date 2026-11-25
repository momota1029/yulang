import Yulang.GeneralDeclarativeI65I72CompletedUnaryBody406

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeHead320 (Equation environment)
open GeneralNominalCenteredHeadMatExpressions (value)
open CommonNominalFullCarrier (Equivalent)
open CommonRecursiveNominalIntervals (ContextWellFormed)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives)
open CommonRoleOutermostResolver (Dictionary Tree Result Summarizes)

/-- The new head does not fit a C365 ModeWindow: its lower is the
given exact completion. Reuse the old State, typed output data and
where children rather than pretending the lower is authored. -/
structure CompletedInvocation406 (s : State) (q : Request) (trees : List Tree) where
  row : Declaration
  needs : List (OutputNeed s)
  forest : SupportForest PriorSource406 s needs
  chosen : PreselectedUnary406 s q row forest
  actualPayload : OriginalPayload406 chosen
  body : CompletedBody406 actualPayload
  fixed : body.Fixed
  clauses : LiteralVariableWhere403 row
  children : WhereForest PriorSource406 s (frameWhereKids400 (originalNativeFrame406 chosen actualPayload)) trees

def CompletedInvocation406.frame {s q trees} (event : CompletedInvocation406 s q trees) :
    AuthoredBodyFrame393 s.core q :=
  originalNativeFrame406 event.chosen event.actualPayload

def CompletedInvocation406.kids {s q trees} (event : CompletedInvocation406 s q trees) : List Request :=
  frameWhereKids400 event.frame

def CompletedInvocation406.visits {s q trees} (event : CompletedInvocation406 s q trees) : List CandidateVisit :=
  event.chosen.visits

/-- A provisional extension, not a change to the original C402
definitions. Old derivations embed literally. This new constructor
uses prior successful finite producers and exact prior where
children in the same State. No model participates in classification. -/
inductive ScopedSource406 (s : State) (q : Request) : Tree → Type where
  | prior {e : Option (Event s q)} : SourceTrace PriorSource406 s q tree e → ScopedSource406 s q tree
  | completed (next : CompletedInvocation406 s q trees) :
      ScopedSource406 s q (.selected next.row.id trees)

def ScopedClassifies406 (s : State) (q : Request) (r : Result) : Prop :=
  ∃ t : Tree, Nonempty (ScopedSource406 s q t) ∧ Summarizes t r

theorem previous_classification_embeds406 {s q result}
    (old : Classifies PriorSource406 s q result) : ScopedClassifies406 s q result := by
  obtain ⟨t,_,⟨trace⟩,summary⟩ := old
  exact ⟨t,⟨.prior trace⟩,summary⟩

theorem completed_invocation_gives_source_verdict406 {s q trees result}
    (invoke : CompletedInvocation406 s q trees)
    (verdict : Summarizes (.selected invoke.row.id trees) result) :
    ScopedClassifies406 s q result :=
  ⟨_,⟨.completed invoke⟩,verdict⟩

/-- Preserve the unfiltered root branch before looking at either
completion, center metadata or where output. -/
theorem raw_k2_forces_new_trace_verdict406 {s q t}
    (raw : RootCycle s q) (trace : ScopedSource406 s q t) : t = .rejected := by
  cases trace with
  | prior old => exact root_k2_forces_original_trace_verdict raw old
  | completed next => exact (next.chosen.rootSafe raw).elim

theorem new_trace_preserves_raw_root_k2_406 {s q} (raw : RootCycle s q) :
    ScopedClassifies406 s q .rejected ∧ ∀ d, ¬ ScopedClassifies406 s q (.selected d) := by
  refine ⟨previous_classification_embeds406 (root_k2_is_rejected_for_every_primitive_system raw),?_⟩
  rintro d ⟨t,⟨source⟩,chosen⟩
  rw [raw_k2_forces_new_trace_verdict406 raw source] at chosen
  cases chosen

/-- The selected typed comparison keeps exact source names in one
model, not equality of two independently found witnesses.
The completed lower is interpreted by the retained assignment; the
authored upper and actual payload use only their original syntax. -/
structure CompletedInvocationMeaning406 {s q trees}
    (event : CompletedInvocation406 s q trees) (m : Model) : Prop where
  lowerMeaning : Equivalent (m.assignment event.chosen.gate.arg.lower).1
    (value (environment m.assignment) .actual (.nominal event.chosen.gate.key [.variable event.chosen.gate.lowerPayload]))
  upperMeaning : m.nativeSyntax event.chosen.gate.upper.slot =
    some (unaryNominalPoint404 event.chosen.gate.key event.chosen.gate.upperPayload)
  lowerWF : ContextWellFormed s.core.modes false (unaryNominalPoint404 event.chosen.gate.key event.chosen.gate.lowerPayload)
  upperWF : ContextWellFormed s.core.modes false (unaryNominalPoint404 event.chosen.gate.key event.chosen.gate.upperPayload)
  comparison : ContextDerives s.core.modes m.assignment false
    (unaryNominalPoint404 event.chosen.gate.key event.chosen.gate.lowerPayload)
    (unaryNominalPoint404 event.chosen.gate.key event.chosen.gate.upperPayload)
  actualPayload : m.nativeSyntax event.actualPayload.source.slot = some
    (unaryNominalPoint404 event.chosen.gate.key (event.frame.input event.chosen.gate.binder).center)
  actualName : (event.frame.input event.chosen.gate.binder).center = event.actualPayload.center
  payloadInInterval : InInterval (m.assignment event.chosen.gate.lowerPayload).1 (m.assignment event.chosen.gate.upperPayload).1
    (m.assignment event.actualPayload.center).1
  outputs : ∀ i : Fin q.demand.outputs.length,
    ExactNamedOutputMeaning401 m (event.body.output i) ∧
    ∃ v, (event.body.output i).receipt.actualEquation m = some (q.demand.outputs[i].target,v) ∧
      Equivalent (m.assignment q.demand.outputs[i].target).1 v

theorem completed_invocation_means_one_state_and_model406 {s q trees}
    (event : CompletedInvocation406 s q trees) (m : Model) (fit : Fits s m) :
    CompletedInvocationMeaning406 event m := by
  obtain ⟨_,lower,upper,lowWF,upWF,compare⟩ := completed_selected_endpoints_have_same_model406 event.chosen m fit
  obtain ⟨_,_,payload,_,_,name,bounds⟩ := original_payload_names_the_exact_native_capture406 event.actualPayload m fit
  exact ⟨lower,upper,lowWF,upWF,compare,payload,name,bounds,
    completed_body_exact_type_and_fixed_in_one_model406 event.body event.fixed m fit⟩

end Yulang.GeneralDeclarativeI65.I72
