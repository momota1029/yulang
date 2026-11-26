import Yulang.GeneralDeclarativeI65I74RetainedInputReplay445

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedFull445.PlacementQA
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem)
open MixedFixed442
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (normalize)
open GeneralDictionaryAssociatedProvenance (Supplies)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

theorem canonical_placement_keeps_same_original_report445 {p : Problem} (source : SourceSelection p) :
    ∃ n : SourceSelection p,
      n.origin.event.frame.placement = unusedPlacement403 ∧
      n.origin.original.original = source.origin.original.original ∧
      n.origin.original.arg = source.origin.original.arg ∧
      n.own.2.out.valueCap = source.own.2.out.valueCap ∧
      eventKey n = eventKey source ∧ sourceReport n = sourceReport source := by
  let r := source.origin
  let a := source.own.2.out
  have authored : (authoredRegistry p.state.core.current).declarations[r.event.frame.ordinal]? =
      some r.decl := by
    rw [← r.exactDecl]
    exact r.event.frame.authored
  let f := frameAtSource395 (originalCandidate r.original).inScope r.event.frame.ordinal authored
    unusedPlacement403 r.original.capture
  have inputs (b : Nat) (one : b = r.original.rowBinder ∨ b = r.original.valueBinder) :
      b ∈ f.decl.inputNames := by
    change b ∈ r.decl.inputNames
    rw [Declaration.inputNames,r.original.written]
    rcases one with h|h <;> simp [h,RefPositions441.pattern,GeneralDeclarationPatterns.normalizeArgs,
      normalize,GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables]
  have caps := exact_ref_output_uses_original_head_centers442 r source.own
  let body : GeneralDeclarations.Equation := ⟨a.bodyId,p.root.demand.outputs[r.i0].name,
    RefPositions441.pattern a.key a.rowBinder a.valueBinder⟩
  have rowSame : r.original.capture a.rowBinder = a.rowCap :=
    (congrArg r.original.capture source.own.2.exactRow).trans (r.original.rowCapture.trans caps.1.symm)
  have valSame : r.original.capture a.valueBinder = a.valueCap :=
    (congrArg r.original.capture source.own.2.exactValue).trans (r.original.valueCapture.trans caps.2.symm)
  have row : f.slots (.explicit body) a.rowBinder = some a.rowCap :=
    (explicit_authored_head_slot395 f r.original.checked.outputOnly (body := body)
      a.rowBinder (inputs _ (.inl source.own.2.exactRow))).trans (congrArg some rowSame)
  have value : f.slots (.explicit body) a.valueBinder = some a.valueCap :=
    (explicit_authored_head_slot395 f r.original.checked.outputOnly (body := body)
      a.valueBinder (inputs _ (.inr source.own.2.exactValue))).trans (congrArg some valSame)
  have supplied : Supplies (authoredRegistry p.state.core.current).roles f.decl
      p.root.demand.outputs[r.i0].name (.explicit body) := by
    change Supplies (authoredRegistry p.state.core.current).roles r.decl
      p.root.demand.outputs[r.i0].name (.explicit body)
    exact r.exactDecl ▸ a.supplied
  let output : OriginalOutput (s := p.state) f r.i0 :=
    ⟨a.key,a.rowBinder,a.valueBinder,a.independent,a.use,a.mode,a.table,a.bodyId,
      supplied,a.original,a.rowCap,a.valueCap,row,value⟩
  have one (i : Fin p.root.demand.outputs.length) : r.i0 = i := Fin.ext (by
    have lt := Nat.lt_of_lt_of_eq i.isLt r.onlyOutput
    change 0 = i.val
    omega)
  let ev : Event p.state p.root := ⟨f,restoreOriginalHead r.original,fun i => one i ▸ output.named⟩
  have noKids : ev.kids = [] := by
    simp [ev,Event.kids,frameWhereKids400,f,frameAtSource395,AuthoredBodyFrame393.clauses,
      r.original.noWhere,children]
  let replay : Replay p := ⟨r.decl,r.original,ev,rfl,r.exactOrdinal,rfl,noKids,r.onlyOutput⟩
  let normal : SourceSelection p :=
    ⟨replay,rfl,⟨_,⟨output,source.own.2.exactKey,source.own.2.exactRow,
      source.own.2.exactValue,rfl⟩⟩⟩
  refine ⟨normal,rfl,rfl,rfl,rfl,rfl,?_⟩
  have exactOld := original_replayed_ref_equates_same_event_output442 r a
  have sameWrites : Check408.encodedEventWrites ev = Check408.encodedEventWrites r.event := by
    unfold Check408.encodedEventWrites
    apply congrArg List.ofFn
    funext i
    have eq := (one i).symm
    subst i
    rw [← exactOld]
    rfl
  change (⟨.selected r.decl.id [],.selected source.dictionary,Check408.encodedEventWrites ev⟩
    : Checker408.Result) = sourceReport source
  rw [sameWrites]
  rfl

theorem chosen_report_witness_without_placement_premise445 (p : FullProblem)
    (a : LocalSelection p.state p.root)
    (header : HeaderReady445 p.state.base.core.current.environment)
    (escape : ∃ table, EscapeReady445 p.state.base.core.current.ordinary
      a.source.origin.original.arg.lower table) :
    ∃ w : Witness, check_full p a.report w = true := by
  obtain ⟨n,place,_,arg,cap,key,report⟩ := canonical_placement_keeps_same_original_report445 a.source
  have indexOf (source : SourceSelection p.old) : source.origin.i0.val = 0 := rfl
  have compare : n.origin.i0 = a.source.origin.i0 := Fin.ext
    ((indexOf n).trans (indexOf a.source).symm)
  let atTarget (i : Fin p.root.demand.outputs.length) : Nat := p.root.demand.outputs[i].target
  have sameTarget := congrArg atTarget compare
  have fresh : FreshOutput n := by
    change atTarget n.origin.i0 ∉ oldReadNames p.state.base.core ∧
      n.own.2.out.valueCap.center ≠ atTarget n.origin.i0
    rw [sameTarget,cap]
    exact a.fresh
  let kept : StoredSelection p.state n :=
    ⟨a.kept.row,a.kept.member,a.kept.shape,a.kept.exactKey.trans key.symm⟩
  let chosen : LocalSelection p.state p.root := ⟨n,fresh,kept,a.single⟩
  obtain ⟨w,sound⟩ := canonical_ready_supplies_witness445 p chosen header place (by rw [arg]; exact escape)
  have exactReport : chosen.report = a.report := report
  exact ⟨w,exactReport ▸ sound⟩

end Yulang.GeneralDeclarativeI65.I72.RetainedFull445.PlacementQA
