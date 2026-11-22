import Yulang.GeneralDeclarativeWitnessTypedChild354
import Yulang.GeneralDeclarativeWitnessCovariantCheckedScope353
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTypedSound354
open GeneralDeclarativeWitnessTypedChild354 (Linked downstream same_row physical_target)
open GeneralDeclarativeWitnessTypedRelease354 (address actual_payload exact_ordinal)
open GeneralDeclarativeWitnessCovariantOrigin353 (Row View assigned HasView)
open GeneralDeclarativeWitnessCovariantCanonical353 (valuation rows_at_interval view_for_every_model)
open GeneralDeclarativeWitnessCovariantInterval353 (typed_interval exact_write_targets)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeEntailment320 (Holds)
open CommonDeclaredNominalInspection (DeclaredSubtype)
open CommonNominalRegularErasure (subtype_monotone)
open GeneralSourceState (Output)

theorem authored_body {i s w} (b : Linked i s w) :
    GeneralDictionaryAssociatedProvenance.Supplies b.writer.output.source.ctx.registry.roles
      b.writer.output.source.ctx.decl b.emitted.atWrite.demand.name
      (.explicit b.emitted.atWrite.typed.authored) := by
  have ids := (splitAnd (splitAnd b.writer.output.source.good).1).2
  have unique := (GeneralDeclarativeWitnessChecks349.identified ids).2.2.1
  exact GeneralDeclarativeWitnessTypedOutput354.supplies b.emitted.atWrite.typed unique

def childView {i s w} (b : Linked i s w) (m : Assignment) :=
  valuation (downstream i b.writer.output.state b.demand b.emitted.atWrite.typed.row) m

theorem released_row_in_child {i s w} (b : Linked i s w) :
    b.emitted.atWrite.typed.row ∈ (downstream i b.writer.output.state b.demand b.emitted.atWrite.typed.row).rows :=
  List.mem_append_right _ List.mem_cons_self

theorem child_models {i s w} (b : Linked i s w) (m : Assignment) :
    ∀ row ∈ (downstream i b.writer.output.state b.demand b.emitted.atWrite.typed.row).rows, HasView m (childView b m) row := by
  have ran := b.ran
  unfold GeneralDeclarativeWitnessCovariantInterval353.decode at ran
  obtain ⟨read,first,_⟩ := GeneralSourceMetadataExprDomain291.bind_success ran
  have clean := rows_at_interval first
  exact view_for_every_model _ m clean

theorem released_type_at_actual_center {i s w} (b : Linked i s w) (m : Assignment) (fit : Models s m) :
    ∃ actual : View,
      childView b m b.receiver.facts.arg.center = some actual ∧
      actual.tag = b.emitted.atWrite.typed.tag ∧ actual.box = b.emitted.atWrite.typed.box ∧
      Common.Equivalent actual.payload
        (.union (assigned m b.writer.output.source.anchor.first.valueName).1
                (assigned m b.writer.output.source.anchor.last.valueName).1) := by
  obtain ⟨found,atCenter,tag,box,payload⟩ :=
    child_models b m _ (released_row_in_child b)
  rw [physical_target b]
  have same := actual_payload b.emitted m fit
  exact ⟨found,atCenter,tag,box,Common.equivalent_trans payload
    ⟨subtype_monotone _ _ same.1,subtype_monotone _ _ same.2⟩⟩

/-- The same independently supplied ordinary model validates both bodies.
The nominal type decoded at the actual child center comes exclusively
from the authorized explicit associated output. -/
theorem both {i s w} (b : Linked i s w) (m : Assignment) (fit : Models s m) :
    (∃ l c h : View,
      childView b m b.receiver.facts.arg.lower = some l ∧
      childView b m b.receiver.facts.arg.center = some c ∧
      childView b m b.receiver.facts.arg.upper = some h ∧
      DeclaredSubtype (table w.childHead.center.box) (View.head l) (View.head c) ∧
      DeclaredSubtype (table w.childHead.center.box) (View.head c) (View.head h)) ∧
    (∀ eq ∈ GeneralDeclarativeWitnessTypedOutput354.ordinary w.writer.trace,Holds m eq) ∧
    w.child.outputRows.map Equation.left = b.demand.outputs.map Output.target ∧
    ∀ eq ∈ w.child.outputRows,Holds m eq := by
  obtain ⟨l,c,h,left,center,right,_,before,after⟩ := typed_interval b.receiver.facts m (childView b m)
    (GeneralDeclarativeWitnessReceipt349.same_model b.writer.check m fit) (child_models b m)
  exact ⟨⟨l,c,h,left,center,right,before,after⟩,(GeneralDeclarativeWitnessTypedPacket354.exact b.writer m fit).2,
    (exact_write_targets b.receiver m fit).2⟩

end Yulang.GeneralDeclarativeWitnessTypedSound354
