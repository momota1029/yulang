import Yulang.GeneralDeclarativeI65Compiler367
import Yulang.GeneralDeclarativeI65Tape367
import Yulang.GeneralDeclarativeI65TypedOutputs365

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (Joined pointSpans context)
open GeneralDeclarativeWitnessCompiler350 (Context Finished preparation whereBatch fixedBatch execute portNames placed)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralPatternVariableProvenance (normalize_args_variables)
open GeneralDeclarations (Declaration)

theorem ran_body_has_literal_ports (c : Context) {f : Finished}
    (ran : execute c = some f) :
    ∃ before ports, preparation c = some (before,ports) ∧
      f.kids = GeneralDeclarativeEmissionForest322.children c.decl (portNames c ports) (placed c ports) := by
  unfold execute at ran
  cases made : preparation c with
  | none => simp [made] at ran
  | some p =>
    obtain ⟨before,ports⟩ := p
    cases clauses : whereBatch c ports with
    | none => simp [made,clauses] at ran
    | some extra =>
      cases fixed : fixedBatch c ports with
      | none => simp [made,clauses,fixed] at ran
      | some rows =>
        have shaped : (⟨GeneralDeclarativeEntailment320.appendFacts before extra,rows,
            GeneralDeclarativeEmissionForest322.children c.decl (portNames c ports) (placed c ports)⟩ :
            Finished) = f := by simpa [made,clauses,fixed] using ran
        cases shaped
        exact ⟨before,ports,rfl,rfl⟩

def actualContext {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (b : BodyFacts s q row kids) : Context :=
  context s.current q.demand row b.body.named b.spans b.body.keep b.body.fallback b.body.targets

theorem receipt_compiler_centers {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (body : BodyFacts s q row kids) (capture : Nat → Capture)
    (separate : row.OutputOnly)
    (seen : ∀ n ∈ row.inputNames, ((body.spans.find? fun entry => entry.1 == n).map Prod.snd) = some (capture n)) :
    ∃ before ports, preparation (actualContext body) = some (before,ports) ∧
      body.demands = GeneralDeclarativeEmissionForest322.children row
        (portNames (actualContext body) ports) (placed (actualContext body) ports) ∧
      ∀ n ∈ row.inputNames, ((portNames (actualContext body) ports).input n).center = (capture n).center := by
  obtain ⟨before,ports,prepare,actual⟩ := ran_body_has_literal_ports (actualContext body) body.body.run
  refine ⟨before,ports,prepare,body.body.children.symm.trans actual,?_⟩
  intro n used
  have noOutput : n ∉ row.outputNames :=
    fun out => separate.1 n out (normalize_args_variables row.head used)
  exact actual_port_center (c := actualContext body) (ports := ports) (seen n used) noOutput

/-- The later body supplies actual generated receipts and established
postselection binder bounds. It cannot be used to create a head match. -/
inductive BodyLayout {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (body : BodyFacts s q row kids) : SourceHead s q row → Prop where
  | ordered {capture head} :
      (∀ n ∈ row.inputNames, Bounds s.current.ordinary (capture n)) →
      (∀ n ∈ row.inputNames, ((body.spans.find? fun entry => entry.1 == n).map Prod.snd) = some (capture n)) →
      BodyLayout body (.ordered capture head)
  | joined {head : Joined s.current q.demand row} :
      body.spans = pointSpans head.firstBinder head.lastBinder head.actualValue →
      BodyLayout body (.joined head)

def authored_node {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (pick : AuthoredCandidate s q row) (body : BodyFacts s q row kids)
    (recipe : BodyLayout body pick.head) : SourceNode s q row kids :=
  ⟨pick.inScope,pick.covered,pick.signature,body,by
    generalize headEq : pick.head = actual at recipe
    cases recipe with
    | ordered bounds traced =>
      exact .ordered _ bounds traced (shallow_head_projection (by assumption))
    | joined atSpans => exact .joined _ atSpans⟩

theorem attached_source_sound {s : State} {q : Request} {row : Declaration} {kids : List Request}
    (pick : AuthoredCandidate s q row) (body : BodyFacts s q row kids)
    (recipe : BodyLayout body pick.head) (m : Model) (fit : Fits s m) :
    HeadModel s m q row pick.head ∧ SourceNodeMeaning (authored_node pick body recipe) m :=
  ⟨source_head_sound pick.head m fit,source_node_sound (authored_node pick body recipe) m fit⟩

end Yulang.GeneralDeclarativeI65
