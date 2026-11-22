import Yulang.GeneralDeclarativeOpenTraversal339
import Yulang.GeneralDeclarativeCompoundDictionary338

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpenSelected339
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeCompoundTree338 (World)
open GeneralDeclarativeCompoundBatch338 (Ticket minted)
open GeneralDeclarativeCompoundRoutes338 (key)
open GeneralDeclarativeCompoundCompiler338 (Selected Node)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeOpenReceipt339 (receipt routed same_open_endpoint)
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarations (Checked)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open CommonNominalFullCarrier (Equivalent)

/-- A current actual selection supplied its old independently justified
ordered input/receipt. This extra open read is about one actual earlier
residual at the same address, not a new candidate or new verdict. -/
theorem output {s : State} {p : Supported s done}
    (selection : Selected p sidecar r i waiting d impl kids)
    {w : World done} (ticket : Ticket w.source arg fields)
    (read : GeneralDeclarativeCompoundOpenPrefix338.Read w.source arg
      ((GeneralDeclarativeCompoundPattern338.layout fields).map Prod.fst) ls us first last le ue)
    (earlier : Extends w.state selection.ordinary)
    (compiled : e ∈ minted w.state w.reads selection.keep ticket.jobs)
    (retained : e ∈ selection.named.reads) (lastJob : key e.1 = none)
    (checked : Checked r) (covered : Coverage r i) (declared : Declared r d)
    (m) (fit : ModelsExact s sidecar m) :
    (∃ cap, Node r i m d impl cap kids selection.spans) ∧ (∀ child ∈ kids, Declared r child) ∧
      receipt m arg ((GeneralDeclarativeCompoundPattern338.layout fields).map Prod.fst) e.2 ∧
      Equivalent (interp m (withTail ls le)) (interp m (withTail ticket.lower ticket.loEnd)) ∧
      Equivalent (interp m (withTail us ue)) (interp m (withTail ticket.upper ticket.hiEnd)) := by
  obtain ⟨node,children⟩ := GeneralDeclarativeCompoundCompiler338.selected_sound selection checked covered declared m fit
  have former := restrict earlier m (relays_models selection.receipt m fit.1)
  exact ⟨node,children,(routed ticket compiled lastJob m former).mp (fit.2 e (selection.retained retained)),
    same_open_endpoint ticket.read read m former⟩

end Yulang.GeneralDeclarativeOpenSelected339
