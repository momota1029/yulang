import Yulang.GeneralDeclarativeWitnessRangeCut355
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessGrandchild355
open GeneralDeclarativeWitnessRangeRelease355 (Released)
open GeneralDeclarativeWitnessTypedReemit354 (Linked)
open GeneralDeclarativeWitnessTypedRelease354 (Authority Location)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem Row)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWitnessCompiler350 (printDemand)
open GeneralNominalCommonBridge (Assignment)

structure Plan where
  authority : Authority
  producer : Location
  writeIndex : Nat
  childIndex : Nat
  authored : List Row
  keep : List Nat
  fallback : Nat → Capture

structure Wire where
  path : List Nat
  head : GeneralDeclarativeWitnessCovariantInterval353.Wire
  output : GeneralDeclarativeWitnessCompiler350.Wire

def stage {i s w} (a : Linked i s w) (p : Plan) (d : Demand) (row : Row) : Problem :=
  { i.producer with
    rows := p.authored ++ [row]
    stage := a.receiver.compiled.state
    demand := d
    keep := p.keep
    fallback := p.fallback }

structure Accepted {i s w} (a : Linked i s w) (p : Plan) (code : Wire) where
  released : Released a p.authority p.producer p.writeIndex
  demand : Demand
  actuallyEmitted : a.receiver.compiled.children[p.childIndex]? = some demand
  exactPath : code.path = p.producer.path ++ [p.childIndex]
  separatesAuthored : released.body.indexed.typed.row.root ∉ p.authored.map Row.root
  actualSlot : code.head.center.center = p.authored.length
  results : GeneralDeclarativeWitnessCovariantInterval353.Checked
    (stage a p demand released.body.indexed.typed.row) code.head s code.output
  ran : GeneralDeclarativeWitnessCovariantInterval353.decode
    (stage a p demand released.body.indexed.typed.row) code.head s code.output = some results
  leaf : results.compiler.compiled.kids = []

def decode {i s w} (a : Linked i s w) (p : Plan) (code : Wire) : Option (Accepted a p code) := do
  let r ← GeneralDeclarativeWitnessRangeRelease355.read a p.authority p.producer p.writeIndex
  match got : a.receiver.compiled.children[p.childIndex]? with
  | none => none
  | some d =>
    if path : code.path = p.producer.path ++ [p.childIndex] then
      if author : r.body.indexed.typed.row.root ∉ p.authored.map Row.root then
        if slot : code.head.center.center = p.authored.length then
          match ran : GeneralDeclarativeWitnessCovariantInterval353.decode (stage a p d r.body.indexed.typed.row)
                code.head s code.output with
          | none => none
          | some verified =>
            if empty : verified.compiler.compiled.kids.isEmpty = true then
              pure ⟨r,d,got,path,author,slot,verified,ran,List.isEmpty_iff.mp empty⟩
            else none
        else none
      else none
    else none

theorem exact_released_read {i s w} {a : Linked i s w} {p code} (ok : Accepted a p code) :
    ok.results.facts.center.anchor.current = ok.released.body.indexed.typed.row := by
  have pos := ok.results.facts.center.anchor.currentAt
  change (p.authored ++ [ok.released.body.indexed.typed.row])[code.head.center.center]? =
    some ok.results.facts.center.anchor.current at pos
  rw [ok.actualSlot,List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at pos
  exact (Option.some.inj pos).symm

theorem exact_target {i s w} {a : Linked i s w} {p code} (ok : Accepted a p code) :
    ok.results.facts.arg.center = ok.released.body.indexed.demand.target := by
  have seen := ok.results.facts.center.anchor.actualCenter
  rw [exact_released_read ok,GeneralDeclarativeWitnessCovariantInterval353.actual_index] at seen
  exact seen.symm

/-- No proof of applicability at 10 arises from an ordinary equality.
For the existing C354 joined schema, a checked grandchild must be on
the exact payload name of the *current* nonpoint child. -/
theorem joint_schema_target_is_payload_name {i s w} {a : Linked i s w} {p code} (ok : Accepted a p code)
    (head : a.receiver.compiled.readFrom.center.decl.head =
      [GeneralDeclarativeWitnessCovariantHead352.rawPattern]) :
    ok.released.body.indexed.demand.target = a.receiver.compiled.readFrom.center.anchor.current.valueName := by
  have children := List.mem_of_getElem? ok.actuallyEmitted
  have arg : ok.results.facts.arg ∈ ok.demand.arguments := by
    have literal := ok.results.facts.shape
    change ok.demand.arguments = [ok.results.facts.arg] at literal
    rw [literal]
    exact List.mem_cons_self
  exact (exact_target ok).symm.trans
    (GeneralDeclarativeWitnessRangeCut355.no_grandchild_at_a_different_fixed_target a.receiver.compiled head children arg)

open GeneralDeclarativeWitnessCovariantOrigin353 (View assigned HasView)
open GeneralDeclarativeWitnessCovariantCanonical353 (valuation rows_at_interval view_for_every_model)
open GeneralDeclarativeWitnessCovariantViews353 (View.head)
open GeneralDeclarativeWitnessCovariantMetadata353 (table)
open CommonDeclaredNominalInspection (DeclaredSubtype)
open GeneralDeclarativeEntailment320 (Holds)

def view {i s w} {a : Linked i s w} {p code} (ok : Accepted a p code) (m : Assignment) :=
  valuation (stage a p ok.demand ok.released.body.indexed.typed.row) m

theorem covers_rows {i s w} {a : Linked i s w} {p code} (ok : Accepted a p code) (m : Assignment) :
    ∀ row ∈ (stage a p ok.demand ok.released.body.indexed.typed.row).rows, HasView m (view ok m) row := by
  have ran := ok.ran
  unfold GeneralDeclarativeWitnessCovariantInterval353.decode at ran
  obtain ⟨_,head,_⟩ := GeneralSourceMetadataExprDomain291.bind_success ran
  exact view_for_every_model _ m (rows_at_interval head)

theorem same_model {i s w} {a : Linked i s w} {p code} (ok : Accepted a p code) (m : Assignment) (fit : Models s m) :
    (∃ lo mid hi : View,
      view ok m ok.results.facts.arg.lower = some lo ∧
      view ok m ok.results.facts.arg.center = some mid ∧
      view ok m ok.results.facts.arg.upper = some hi ∧
      DeclaredSubtype (table code.head.center.box) (View.head lo) (View.head mid) ∧
      DeclaredSubtype (table code.head.center.box) (View.head mid) (View.head hi) ∧
      mid.tag = ok.released.body.indexed.typed.row.tag ∧
      mid.box = ok.released.body.indexed.typed.row.box ∧
      Common.Equivalent mid.payload
        (.union (assigned m a.writer.output.source.anchor.first.valueName).1
                (assigned m a.writer.output.source.anchor.last.valueName).1)) ∧
    code.output.outputRows.map GeneralDeclarativeHead320.Equation.left =
      ok.demand.outputs.map GeneralSourceState.Output.target ∧
    ∀ e ∈ code.output.outputRows,Holds m e := by
  have built := GeneralDeclarativeWitnessReceipt349.same_model a.receiver.verifies m fit
  obtain ⟨l,c,h,ll,cc,hh,_,lh,rh⟩ :=
    GeneralDeclarativeWitnessCovariantInterval353.typed_interval ok.results.facts m (view ok m) built (covers_rows ok m)
  obtain ⟨v,actual,tag,box,payload⟩ := covers_rows ok m ok.released.body.indexed.typed.row
    (List.mem_append_right _ List.mem_cons_self)
  have root : ok.released.body.indexed.typed.row.root = ok.released.body.indexed.demand.target := rfl
  rw [root,← exact_target ok] at actual
  have equal := Option.some.inj (actual.symm.trans cc)
  subst v
  have eq := (GeneralDeclarativeWitnessRangeRelease355.exact_payload ok.released m fit).2.2.2
  have join := Common.equivalent_trans payload
    ⟨CommonNominalRegularErasure.subtype_monotone _ _ eq.1,CommonNominalRegularErasure.subtype_monotone _ _ eq.2⟩
  exact ⟨⟨l,c,h,ll,cc,hh,lh,rh,tag,box,join⟩,
    (GeneralDeclarativeWitnessCovariantInterval353.exact_write_targets ok.results m fit).2⟩

end Yulang.GeneralDeclarativeWitnessGrandchild355
