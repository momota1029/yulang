import Yulang.GeneralRebaseReceiptWire289

/-! Pure extraction from the current raw journal. Archive plan count is
not used; the producing effect, actual generation edge and current
candidate report have distinct fields. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseReceiptExtract289
open GeneralDeclarations (Registry Declaration)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalVersionedFrame231 (children)
open GeneralRebaseExecutableRequests262 (requests)
open GeneralRebaseReceiptWire289

def effectSummary (e : Effect roles) : Producer :=
  ⟨e.registry.declarations,e.plan.packet.site.occurrence.identity,e.plan.packet.declaration.id,
    (children e.plan.packet).map Occurrence.identity,
    (requests e.snapshot e.plan.packet.site.occurrence).map GeneralSourceState.Output.target⟩

def candidates (r : Registry) (o : Occurrence roles) : List Declaration :=
  r.declarations.filter (fun d => d.role == o.demand.role)

def diagnostic (ctx : GeneralNominalCandidates.Context) (focus : Occurrence roles)
    (d : Declaration) : Option Inspection :=
  (arguments ctx (inputs focus)).map fun bounds =>
    let inspected := report ctx d bounds
    ⟨!inspected.blocked.isEmpty,!inspected.conflicts.isEmpty,!inspected.arity.isEmpty⟩

def rootRecorded (ctx : GeneralNominalCandidates.Context) (focus : Occurrence roles) : Bool :=
  match arguments ctx (inputs focus) with
  | none => false
  | some bounds => bounds.all fun pair => (ctx.state.nominals pair.1).isSome

def extract (r : Registry) (state : State roles) (focus : Occurrence roles) : Wire :=
  let ctx := state.core.erased.current.context
  let found := candidates r focus
  ⟨r.declarations,state.effects.map effectSummary,
    state.core.erased.current.edges.map fun (up,down) => (up.identity,down.identity),
    focus.identity,found,(requests state.core focus).map GeneralSourceState.Output.target,
    rootRecorded ctx focus,
    match found with
    | [d] => diagnostic ctx focus d
    | _ => none⟩

theorem diagnostic_finished {ctx : GeneralNominalCandidates.Context} {focus : Occurrence roles}
    {d : Declaration} {bounds} (found : arguments ctx (inputs focus) = some bounds) :
    (∃ f, diagnostic ctx focus d = some f ∧ f.finished = true) ↔
      GeneralNominalRecursiveInspection.Finished (report ctx d bounds) := by
  unfold diagnostic Inspection.finished GeneralNominalRecursiveInspection.Finished
  rw [found]
  simp [List.isEmpty_iff,and_assoc]

end Yulang.GeneralRebaseReceiptExtract289
