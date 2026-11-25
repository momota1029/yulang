import Yulang.GeneralDeclarativeI65I75ProjectedReceiptCoherence425

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open Checker408 (Problem)
open CommonNominalFullCarrier (Ty Equivalent record mask)
open GeneralDeclarativeWhere319 (InInterval)
open GeneralDeclarativeRecordChannel330 (project)

/-- Endpoint provenance in terms of the replay key itself. This is
syntax in the given State, not a constraint on a model or a selected flag. -/
def ProjectedReceiptKey425.OriginalSites (key : ProjectedReceiptKey425)
    (s : GeneralDeclarativeI65.State) : Prop :=
  ∃ lo hi : Origin,
    lo ∈ s.origins ∧ hi ∈ s.origins ∧
    lo.slot = key.site.lower ∧ hi.slot = key.site.upper ∧
    lo.issuer = key.site.lowerIssuer ∧ hi.issuer = key.site.upperIssuer ∧
    lo.endpoint = .ordinary (.record key.site.label (.var key.site.fieldLower)
      (.var key.site.tailLower)) ∧
    hi.endpoint = .ordinary (.record key.site.label (.var key.site.fieldUpper)
      (.var key.site.tailUpper))

/-- A successful projected read retains both actual source occurrences,
not merely the width of two denotationally equivalent record values. -/
theorem accepted_projected_receipt_names_both_original_endpoint_sources425
    {p : Problem} {wire key data}
    (read : readProjectedReceipt425 p wire key = some data) :
    key.OriginalSites p.state.core := by
  have exactKey := (read_projected_receipt_is_exact425.mp read).2
  subst key
  have upper := data.original.high.writtenForm
  rw [data.original.sameLabel] at upper
  exact ⟨data.original.low.original,data.original.high.original,data.original.low.owned,
    data.original.high.owned,data.original.low.slotEq,data.original.high.slotEq,
    rfl,rfl,data.original.low.writtenForm,upper⟩

/-- The reported projection is that of the unique actual visible
declaration in this scoped reader. This is the original written field
use, not a selected outcome or report derived from a model. -/
theorem accepted_key_is_exact_original_literal_field_use425
    {p : Problem} {wire key data}
    (read : readProjectedReceipt425 p wire key = some data) :
    p.root.demand.arguments = [⟨key.site.lower,key.site.center,key.site.upper⟩] ∧
    visible p.state.core p.root = [data.original.decl] ∧
    data.original.decl.head =
      [.record key.site.label (.var key.site.fieldBinder) (.var key.site.tailBinder)] ∧
    data.original.decl.associated =
      [⟨key.associatedEquationId,key.outputName,.var key.site.fieldBinder⟩] ∧
    data.original.decl.requirements = [] ∧ data.original.decl.outputBinders = [] := by
  have original := (read_projected_receipt_is_exact425.mp read).2
  subst key
  let r := data.original
  have exactAssoc :
      r.assoc = ⟨r.assoc.id,p.root.demand.outputs[r.outIndex].name,.var r.fieldBinder⟩ := by
    have outputName := r.outputName.symm
    have rhsShape := r.assocRhs
    generalize kept : r.assoc = exactEq at outputName rhsShape ⊢
    cases exactEq with
    | mk id name rhs =>
      change name = _ at outputName
      change rhs = _ at rhsShape
      rw [outputName,rhsShape]
      rfl
  exact ⟨r.request,r.only,r.literal,r.actualAssoc.trans (congrArg (fun x => [x]) exactAssoc),
    r.noWhere,r.noOutBinders⟩

/-- The eventual report can interpret the symbolic receipt independently
of which retained-row proof the checker read. Both original intervals
and the mask refer to the same actual model and record center. -/
structure ProjectedReceiptKey425.Meaning (key : ProjectedReceiptKey425) (m : I72.Model) : Prop where
  required : ∃ a,
    key.valueAt m = some a ∧
    InInterval (m.assignment key.site.fieldLower).1 (m.assignment key.site.fieldUpper).1 a ∧
    Equivalent (m.assignment key.fixedTarget).1 a
  optional : ∃ b,
    project key.site.label true [] (m.assignment key.site.center).1 = some b ∧
    InInterval (m.assignment key.site.fieldLower).1 (m.assignment key.site.fieldUpper).1 b
  residual : InInterval
    (mask [key.site.label] (record key.site.label (m.assignment key.site.fieldLower).1
      (m.assignment key.site.tailLower).1))
    (mask [key.site.label] (record key.site.label (m.assignment key.site.fieldUpper).1
      (m.assignment key.site.tailUpper).1))
    (mask [key.site.label] (m.assignment key.site.center).1)

/-- The exact key has the full projected capture semantics without a
model-dependent or fake captured name in the original wire. Moreover the
actual B6 source reads its real required observation at the original
output coordinates, not merely an equivalent retained variable. -/
theorem accepted_exact_key_denotes_full_projected_capture425
    {p : Problem} {wire key data}
    (read : readProjectedReceipt425 p wire key = some data)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    key.Meaning m ∧ ∃ a,
      key.valueAt m = some a ∧
      data.typed.actualRightValue m =
        some (key.occurrence,key.declarationOrdinal,key.outputOrdinal,key.fixedTarget,a) := by
  have keyEq := (read_projected_receipt_is_exact425.mp read).2
  subst key
  obtain ⟨channels,value,kept⟩ :=
    prepared_write_preserves_full_projected_capture_and_actual_value423 data m fit
  refine ⟨⟨⟨channels.required,channels.atRequired,channels.requiredBounds,kept⟩,
    ⟨channels.optional,channels.atOptional,channels.optionalBounds⟩,channels.residualBounds⟩,?_⟩
  exact ⟨channels.required,channels.atRequired,value⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
