import Yulang.GeneralDeclarativeI65I75ActualOutputBranch425
import Yulang.GeneralDeclarativeI65I75ProjectedCoreReadback425

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open Check408 (Write)
open Checker408 (Problem)

/-- A projected output from authored source by itself is enough to
give the exact symbolic key; proof of a retained row is separate. -/
def keyFromCoreOutput425
    {s : GeneralDeclarativeI65.State} {atlas : B6OccurrenceAtlas401 s} {q i}
    (o : ProjectedCore425.Output s atlas q i) : ProjectedReceiptKey425 :=
  let target := q.demand.outputs[i]
  ⟨q.occurrence,o.ordinal,o.row.id,o.assoc.id,i.val,target.name,target.target,
    ⟨o.fieldBinder,o.tailBinder,o.label,o.arg.lower,o.arg.center,o.arg.upper,o.head.lower.field,
      o.head.upper.field,o.head.lower.residual,o.head.upper.residual,
      o.head.lower.origin.issuer,o.head.upper.origin.issuer⟩⟩

/-- Proposed common output serialization. The named side is exactly
the existing real encoder. The projected side has no field for a
retained variable address or a model. No public tag is allocated. -/
def encodeActualOutput425
    {s : GeneralDeclarativeI65.State} {atlas : B6OccurrenceAtlas401 s} {q i row ord}
    (tag : Nat) (o : OutputBranch425.ActualOutput atlas q i row ord) : Write :=
  match o with
  | .named f original =>
    ⟨q.occurrence,f.ordinal,i.val,q.demand.outputs[i],original.body,Check408.encodeRhs original.rhs⟩
  | .projected original =>
    ⟨q.occurrence,original.ordinal,i.val,q.demand.outputs[i],.explicit original.assoc,
      encodeProjectedKey425 tag (keyFromCoreOutput425 original)⟩

/-- The existing actual Event wire is byte-structurally preserved by
the proposed named route for every legacy event and ordered output. -/
theorem all_legacy_event_writes_are_unchanged_in_named_route425
    {s : I72.State} {q : I72.Request} (e : Event s q) (tag : Nat) :
    List.ofFn (fun (i : Fin q.demand.outputs.length) =>
      encodeActualOutput425 tag (.named e.frame (e.outputs i))) = Check408.encodedEventWrites e :=
  rfl

private def originCoordinates425 {s slot label}
    (recorded : EndpointHead423.Original s slot label) : Nat × Nat × List Nat :=
  (recorded.field,recorded.residual,recorded.origin.issuer)

private theorem cast_origin_preserves_coordinates425 {s slot lo hi}
    (written : EndpointHead423.Original s slot hi) (same : lo = hi) :
    originCoordinates425 (Eq.mpr (congrArg (EndpointHead423.Original s slot) same) written) =
      originCoordinates425 written := by
  cases same
  rfl

private theorem upper_original_coordinates425 {p : Problem} (r : RecordEndpoints422.Read p) :
    originCoordinates425 (upperOriginal423 r) =
      (r.high.field,r.high.residual,r.high.original.issuer) := by
  let raw : EndpointHead423.Original p.state.core r.arg.upper r.high.label :=
    ⟨r.high.field,r.high.residual,r.high.original,r.high.owned,r.high.slotEq,
      r.high.writtenForm,r.high.row⟩
  change originCoordinates425 (Eq.mpr
    (congrArg (EndpointHead423.Original p.state.core r.arg.upper) r.sameLabel.symm) raw) =
      originCoordinates425 raw
  exact cast_origin_preserves_coordinates425 raw r.sameLabel.symm

theorem retained_row_does_not_change_the_core_source_key425
    {p : Problem} (d : PreparedWrite p) :
    keyFromCoreOutput425 (originalProjectedCoreOutput425 d) = projectedKey425 d := by
  have fields := upper_original_coordinates425 d.original
  have a := congrArg Prod.fst fields
  have b := congrArg (fun x : Nat × Nat × List Nat => x.2.1) fields
  have c := congrArg (fun x : Nat × Nat × List Nat => x.2.2) fields
  change (upperOriginal423 d.original).field = d.original.high.field at a
  change (upperOriginal423 d.original).residual = d.original.high.residual at b
  change (upperOriginal423 d.original).origin.issuer = d.original.high.original.issuer at c
  simp only [keyFromCoreOutput425,originalProjectedCoreOutput425,endpointInputs423,
    lowerOriginal423,projectedKey425,a,b,c]

/-- On the exact prepared route, the source-only common serializer
produces the previously verified Write without relying on retained
coordinates or solved values in the symbolic payload. -/
theorem authored_core_and_PreparedWrite_emit_the_same_exact_write425
    {p : Problem} (d : PreparedWrite p) (tag : Nat) :
    encodeActualOutput425 tag (.projected (originalProjectedCoreOutput425 d)) =
      encodeProjectedWrite425 tag d := by
  change _ = _
  simp only [encodeActualOutput425,encodeProjectedWrite425,retained_row_does_not_change_the_core_source_key425]
  rfl

/-- Recover the acyclic input directly from original authored and
typed source, *without* consulting any claimed output/retention proof. -/
def coreOutputFromSource425 {p : Problem} (r : RecordEndpoints422.Read p)
    (typed : RecordEndpoints422.ProjectedOutput r) :
    ProjectedCore425.Output p.state.core p.state.b6 p.root r.outIndex :=
  ⟨r.arg,r.request,r.low.label,endpointInputs423 r,r.fieldBinder,r.residualBinder,r.distinct,
    r.decl,r.only,r.ordinal,r.actualDecl,r.literal,r.assoc,typed.sourceBody,r.assocRhs,
    typed.plan,typed.originalCompiled⟩

def readCoreBeforeRetention425 (p : Problem) (wire : RecordEndpoints422.Wire) :
    Option (Σ i : Fin p.root.demand.outputs.length,
      ProjectedCore425.Output p.state.core p.state.b6 p.root i) := do
  let r ← RecordEndpoints422.readEndpoints422 p wire
  let typed ← RecordEndpoints422.readProjectedOutput422 r
  pure ⟨r.outIndex,coreOutputFromSource425 r typed⟩

/-- Successful retention is coherent with the independently observable
original source. This does not derive retention or election from
that source-only read in the opposite direction. -/
theorem retained_replay_uses_same_core_observed_before_retention425
    {p : Problem} {wire : PrepareWire} {data : PreparedWrite p}
    (read : readRetainedPickWrite423 p wire = some data) :
    readCoreBeforeRetention425 p wire.authored =
      some ⟨data.original.outIndex,originalProjectedCoreOutput425 data⟩ := by
  simp only [readRetainedPickWrite423,Option.bind_eq_bind,Option.bind_eq_some_iff,
    Option.pure_def] at read
  obtain ⟨found,source,typed,term,retained,whereRow,done⟩ := read
  cases Option.some.inj done
  simp [readCoreBeforeRetention425,source,term,coreOutputFromSource425,
    originalProjectedCoreOutput425]

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
