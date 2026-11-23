import Yulang.GeneralDeclarativeI65JoinBody368

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralDeclarativeWitnessTypedOutput354 (Write ordinary)
open GeneralDeclarativeWitnessCompiler350 (Context portNames placed)
open GeneralDeclarativeWitnessDeclaredState357 (Value authoredRegistry emitted_declared)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarations (Declaration)

/-- The head is already justified on the exact source, independently
of which compiler emits the literal receipt. Mixed writes retain their
types and order instead of masquerading as ordinary equations. -/
inductive SourceReceipt {s : State} {q : Request} {row : Declaration}
    (pick : AuthoredCandidate s q row) (kids : List Request) : Type where
  | ordinary (body : BodyFacts s q row kids) : BodyLayout body pick.head → SourceReceipt pick kids
  | mixed {ctx : Context} {p : Problem}
      (body : TypedWritten (s := s) (q := q) (decl := row) ctx p kids) :
      TypedSelectedLayout ctx.spans pick.head → SourceReceipt pick kids

def SourceReceipt.trace {s : State} {q : Request} {row : Declaration}
    {pick : AuthoredCandidate s q row} {kids : List Request} : SourceReceipt pick kids → List Write
  | .ordinary body _ => body.body.finished.fixed.map Write.ordinary
  | .mixed body _ => body.outputs.trace

def SourceReceipt.demands {s : State} {q : Request} {row : Declaration}
    {pick : AuthoredCandidate s q row} {kids : List Request} : SourceReceipt pick kids → List Demand
  | .ordinary body _ => body.demands
  | @SourceReceipt.mixed _ _ _ _ _ ctx _ body _ =>
    GeneralDeclarativeEmissionForest322.children ctx.decl
      (portNames ctx body.ports) (placed ctx body.ports)

theorem trace_of_only_ordinary (rows : List Equation) :
    ordinary (rows.map Write.ordinary) = rows := by
  induction rows with
  | nil => rfl
  | cons head tail ih =>
    change head :: ordinary (tail.map Write.ordinary) = head :: tail
    rw [ih]

structure ReceiptMeaning {s : State} {q : Request} {row : Declaration}
    {pick : AuthoredCandidate s q row} {kids : List Request}
    (receipt : SourceReceipt pick kids) (m : Model) : Prop where
  read : HeadModel s m q row pick.head
  ordered : kids = children q receipt.demands
  declared : ∀ d ∈ receipt.demands, Declared (authoredRegistry s.current) d
  targets : receipt.trace.map Write.target = q.demand.outputs.map GeneralSourceState.Output.target
  equations : ∀ e ∈ ordinary receipt.trace, Holds m.assignment e
  nominal : ∀ r, .typed r ∈ receipt.trace →
    ∃ v : Value, m.authoredValues r.root = some v ∧ v.tag = r.tag ∧ v.name = r.box ∧
      v.arguments = [.inl (m.assignment r.valueName).1]

theorem source_receipt_in_one_model {s : State} {q : Request} {row : Declaration}
    {pick : AuthoredCandidate s q row} {kids : List Request}
    (receipt : SourceReceipt pick kids) (m : Model) (fit : Fits s m) :
    ReceiptMeaning receipt m := by
  cases receipt with
  | ordinary body layout =>
    have head := source_head_sound pick.head m fit
    obtain ⟨bodyTargets,fixed⟩ := body_facts_sound body m fit
    have targets : (SourceReceipt.trace (.ordinary body layout)).map Write.target =
        q.demand.outputs.map GeneralSourceState.Output.target := by
      simpa only [SourceReceipt.trace,List.map_map,Function.comp_def,Write.target]
        using bodyTargets
    refine ⟨head,body.order,children_are_actual_requests body pick.signature,targets,?_,?_⟩
    · intro e there
      exact fixed e (by simpa only [SourceReceipt.trace,trace_of_only_ordinary] using there)
    · intro r there
      obtain ⟨term,_,impossible⟩ := List.mem_map.mp there
      cases impossible
  | @mixed ctx p body layout =>
    have meaning := chosen_typed_literal_body_sound pick body layout m fit
    refine ⟨meaning.head,meaning.exactKids,?_,meaning.fixedTargets,meaning.ordinaryRows,meaning.typedRows⟩
    have sig : ctx.decl.Signature ctx.registry.roles := by
      rw [body.contextRow,body.currentSource]
      exact pick.signature
    intro d used
    have named := emitted_declared (c := ctx) (ports := body.ports) sig used
    exact body.currentSource ▸ named

end Yulang.GeneralDeclarativeI65
