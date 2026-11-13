import Yulang.GeneralNominalSettledSteps
import Yulang.GeneralNominalFreshPump
import Yulang.GeneralNominalDownstreamSiblingFixture

/-! Deleting an unfinished packet's output is a genuine model test for the
new guard. The first pump-child theorem exposes its packet-prefix and read
interface explicitly; it does not construct the P/E/W installation prefix. -/
namespace Yulang.GeneralNominalSettledPump
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralNominalSettledSupport (Trusted PacketSettled Unsettled HeadJustified)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Test)

/-- A model of the journal after deleting just one packet's output facts.
Unlike deleting an occurrence's entire support cone, this preserves all input
facts, output-routing facts from other packets, and same-input merge equations. -/
structure OutputCut (state : Tracked roles) (producer : Packet roles) (model : Assignment) : Prop where
  source : GeneralNominalState.Models state.source.state model
  facts : ∀ fact ∈ state.facts, (∀ support, fact ≠ Fact.outputs producer support) → fact.Holds model

theorem cut_models (cut : OutputCut state producer model) (unfinished : Unsettled state.current producer)
    (trusted : Trusted state facts) : GeneralNominalSettledSupport.Models state facts model := by
  refine ⟨cut.source,?_⟩
  intro fact member
  apply cut.facts fact (GeneralNominalSettledSupport.trusted_members trusted fact member)
  intro support equal
  exact GeneralNominalSettledSupport.no_unsettled_output trusted unfinished (equal ▸ member)

theorem cut_excludes_nominal (cut : OutputCut state producer model)
    (unfinished : Unsettled state.current producer) (scalar : (model identity).1 = .base .int) :
    ¬ HeadJustified state identity (.nominal name arity) := by
  rintro ⟨facts,trusted,snapshot,observation,head,entailed⟩
  have valid := entailed model (cut_models cut unfinished trusted)
  generalize tagEq : Test.nominal name arity = tag at head
  cases head with
  | scalar => cases tagEq
  | structural => cases tagEq
  | nominal slot descriptor recorded =>
    cases tagEq
    obtain ⟨arguments,_,equal⟩ := valid
    rw [scalar] at equal
    exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (equal.1 0) 0
      ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead _ arguments.length) ⟨rfl,by simp⟩

/-- A checked interface for the first failed inspection. The descriptor may
already be present through full-journal refresh; a cached head is insufficient. -/
structure InspectionPoint (registry : Registry) (state : Tracked roles) (focus : Occurrence roles) where
  declaration : Declaration
  visible : declaration ∈ registry.declarations
  role : declaration.role = focus.demand.role
  bounds : List (GeneralNominalInspection.Bounds state.current.context.state)
  located : GeneralNominalRecursiveCandidates.arguments state.current.context focus = some bounds
  slot : Fin state.current.context.state.base.slots
  inspected : slot ∈ readsMany state.current.context.state
    (GeneralNominalInspection.queries state.current.context.state state.current.context.interpretation declaration) bounds
  descriptor : GeneralNominalState.Descriptor state.current.context.state.base.slots
  recorded : state.current.context.state.nominals slot = some descriptor

theorem inspected_cut_pending (point : InspectionPoint registry state focus)
    (cut : OutputCut state producer model) (unfinished : Unsettled state.current producer)
    (scalar : (model (state.current.context.state.base.source point.slot)).1 = .base .int) :
    GeneralNominalSettledSteps.SupportPending registry state focus := by
  intro guard
  obtain ⟨test,observation,head,justified⟩ :=
    guard.2 point.declaration point.visible point.role point.bounds point.located point.slot point.inspected
  have tag := GeneralNominalDownstreamSiblingFixture.nominal_test_unique _ point.slot point.descriptor
    point.recorded test observation head
  rw [tag] at justified
  exact cut_excludes_nominal cut unfinished scalar justified

open GeneralNominalFreshPumpDeclarations (roles registry)

/-- The source side of this interface is the existing checked pump source.
The remaining fields are concrete obligations for its finite P/E/W prefix,
not an assumption of the desired noninstallation conclusion. -/
structure FirstPrefix (state : Tracked roles) (w : Packet roles) where
  source : state.source = GeneralNominalFreshPump.context
  w_unsettled : Unsettled state.current w
  model : Assignment
  tail : (model 3).1 = .base .int
  source_valid : GeneralNominalState.Models GeneralNominalFreshPump.state model
  other_facts : ∀ fact ∈ state.facts, (∀ support, fact ≠ Fact.outputs w support) → fact.Holds model

theorem first_prefix_cut (certificate : FirstPrefix state w) : OutputCut state w certificate.model :=
  ⟨by simpa only [certificate.source] using certificate.source_valid,certificate.other_facts⟩

/-- P1 reads A0 (source identity 3) while matching its second list layer.
This theorem applies even after W0's provisional equation has been refreshed
into a recorded descriptor there. The finite-prefix certificate remains explicit. -/
theorem first_recursive_child_not_installable {state : Tracked roles} {w child : Packet roles}
    (certificate : FirstPrefix state w) (point : InspectionPoint registry state child.site.occurrence)
    (tail_read : state.current.context.state.base.source point.slot = 3) :
    ¬ GeneralNominalSettledSteps.Installable registry state child := by
  apply GeneralNominalSettledSteps.pending_not_installable
  apply inspected_cut_pending point (first_prefix_cut certificate) certificate.w_unsettled
  simpa only [tail_read] using certificate.tail

/-- Formation of the original source also holds for the new relation. -/
theorem pump_source_formed : GeneralNominalSettledSteps.SourceFormed registry
    GeneralNominalFreshPump.root GeneralNominalFreshPump.start :=
  .initial GeneralNominalFreshPump.context GeneralNominalFreshPump.initial_source

end Yulang.GeneralNominalSettledPump
