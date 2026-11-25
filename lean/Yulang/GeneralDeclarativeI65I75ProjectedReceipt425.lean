import Yulang.GeneralDeclarativeI65I75EndpointHeadReadback423

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open Checker408 (Problem)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralDeclarativeRecordChannel330 (project)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralSourceState (Output)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

structure ProjectionSite425 where
  fieldBinder : Nat
  tailBinder : Nat
  label : Nat
  lower : Nat
  center : Nat
  upper : Nat
  fieldLower : Nat
  fieldUpper : Nat
  tailLower : Nat
  tailUpper : Nat
  lowerIssuer : List Nat
  upperIssuer : List Nat
  deriving DecidableEq, Repr

/-- Internal replay data, not a new accepted public TypeWire tag.
It describes the original projected use, never a variable chosen
to represent its value in an already-retained ordinary equation. -/
structure ProjectedReceiptKey425 where
  occurrence : List Nat
  declarationOrdinal : Nat
  declarationId : Nat
  associatedEquationId : Nat
  outputOrdinal : Nat
  outputName : Nat
  fixedTarget : Nat
  site : ProjectionSite425
  deriving DecidableEq, Repr

def projectedKey425 {p : Problem} (w : PreparedWrite p) : ProjectedReceiptKey425 :=
  let r := w.original
  let out := p.root.demand.outputs[r.outIndex]
  ⟨p.root.occurrence,r.ordinal,r.decl.id,r.assoc.id,r.outIndex.val,out.name,out.target,
    ⟨r.fieldBinder,r.residualBinder,r.low.label,r.arg.lower,r.arg.center,r.arg.upper,
      r.low.field,r.high.field,r.low.residual,r.high.residual,r.low.original.issuer,r.high.original.issuer⟩⟩

def ProjectedReceiptKey425.valueAt (a : ProjectedReceiptKey425) (m : I72.Model) : Option Ty :=
  project a.site.label false [] (m.assignment a.site.center).1

def readProjectedReceipt425 (p : Problem) (wire : PrepareWire) (key : ProjectedReceiptKey425) :
    Option (PreparedWrite p) := do
  let data ← readRetainedPickWrite423 p wire
  if projectedKey425 data = key then some data else none

theorem read_projected_receipt_is_exact425 {p : Problem} {wire key data} :
    readProjectedReceipt425 p wire key = some data ↔
      readRetainedPickWrite423 p wire = some data ∧ projectedKey425 data = key := by
  cases h : readRetainedPickWrite423 p wire with
  | none => simp [readProjectedReceipt425,h]
  | some found =>
    by_cases eq : projectedKey425 found = key
    · simp [readProjectedReceipt425,h,eq]
      intro id
      simpa [id] using eq
    · simp [readProjectedReceipt425,h,eq]
      intro e
      simpa [e] using eq

/-- The key is related to the actual typed body from the compiler atlas.
It does not attest to a body chosen by the reporting witness. -/
theorem exact_key_checks_original_B6_source425 {p : Problem} {wire key data}
    (read : readProjectedReceipt425 p wire key = some data) :
    key.occurrence = p.root.occurrence ∧
    (authoredRegistry p.state.core.current).declarations[key.declarationOrdinal]? =
      some data.original.decl ∧
    key.declarationId = data.original.decl.id ∧
    key.associatedEquationId = data.original.assoc.id ∧
    data.original.decl.associated = [data.original.assoc] ∧
    key.outputOrdinal = data.original.outIndex.val ∧
    key.outputName = p.root.demand.outputs[data.original.outIndex].name ∧
    key.fixedTarget = p.root.demand.outputs[data.original.outIndex].target ∧
    GeneralDictionaryAssociatedProvenance.lookup
      (authoredRegistry p.state.core.current).roles data.original.decl key.outputName =
      some (.explicit data.original.assoc) ∧
    p.state.b6.read p.root key.declarationOrdinal data.original.outIndex
      (.explicit data.original.assoc) = some data.typed.plan := by
  have eq := (read_projected_receipt_is_exact425.mp read).2
  subst key
  exact ⟨rfl,data.original.actualDecl,rfl,rfl,data.original.actualAssoc,rfl,rfl,rfl,data.typed.sourceBody,
    data.typed.originalCompiled⟩

/-- The same reported projection evaluates the actual original B6
plan in the given model. A retained variable may be equivalent but
is not part of the identity of that authored projection. -/
theorem read_projected_receipt_keeps_real_original_equation425
    {p : Problem} {wire key data}
    (read : readProjectedReceipt425 p wire key = some data)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    let pos := data.retained.rowAt
    p.state.core.current.ordinary.equations[pos.1]? =
      some ⟨key.fixedTarget,.variable pos.2⟩ ∧
    ∃ v : Ty, key.valueAt m = some v ∧
      data.typed.actualRightValue m =
        some (key.occurrence,key.declarationOrdinal,key.outputOrdinal,key.fixedTarget,v) ∧
      Equivalent (m.assignment key.fixedTarget).1 v ∧
      Equivalent (m.assignment pos.2).1 v := by
  have eq := (read_projected_receipt_is_exact425.mp read).2
  subst key
  have row := exact_literal_target_row_of_prepared_write423 data
  obtain ⟨channels,value,kept⟩ :=
    prepared_write_preserves_full_projected_capture_and_actual_value423 data m fit
  have raw : Equivalent (m.assignment (projectedKey425 data).fixedTarget).1
      (m.assignment data.retained.rowAt.2).1 :=
    fit.1.1.2 _ (List.mem_of_getElem? row)
  exact ⟨row,channels.required,channels.atRequired,value,kept,
    eqv_trans ⟨raw.2,raw.1⟩ kept⟩

open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeOutputs320 (bodyPattern)

/-- This C14 case carries the original normalized binder constructor,
not merely a plan with the same denotation. -/
theorem exact_B6_plan_is_original_projected_binder425
    {s : GeneralDeclarativeI65.State} {pat : Pattern}
    (plan : B6MixedRhs401 s false pat) {binder : Nat} (eq : pat = .var binder) :
    (eq ▸ plan : B6MixedRhs401 s false (.var binder)) = .binder binder () := by
  cases eq
  cases plan
  rfl

theorem read_projected_receipt_keeps_literal_plan425
    {p : Problem} {wire key data}
    (read : readProjectedReceipt425 p wire key = some data) :
    ∃ eq : normalize (bodyPattern (.explicit data.original.assoc)) = .var key.site.fieldBinder,
      (eq ▸ data.typed.plan : B6MixedRhs401 p.state.core false (.var key.site.fieldBinder)) =
        .binder key.site.fieldBinder () := by
  have equal := (read_projected_receipt_is_exact425.mp read).2
  subst key
  have eq : normalize (bodyPattern (.explicit data.original.assoc)) = .var data.original.fieldBinder := by
    change normalize data.original.assoc.rhs = _
    rw [data.original.assocRhs]
    rfl
  exact ⟨eq,exact_B6_plan_is_original_projected_binder425 _ eq⟩

/-- The original field and residual bounds are semantic proofs in the
same model as the exact B6 receipt, not premises used to read a key. -/
theorem verified_projected_receipt_has_same_fit_head_and_final_target425
    {p : Problem} {wire key data}
    (read : readProjectedReceipt425 p wire key = some data)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    EndpointHead423.Meaning (endpointInputs423 data.original) m ∧
    ∃ v : Ty, key.valueAt m = some v ∧
      data.typed.actualRightValue m =
        some (key.occurrence,key.declarationOrdinal,key.outputOrdinal,key.fixedTarget,v) ∧
      Equivalent (m.assignment key.fixedTarget).1 v := by
  have source := EndpointHead423.source_endpoints_have_projected_meaning423
    (endpointInputs423 data.original) m fit
  obtain ⟨_,v,e,q,target,_⟩ :=
    read_projected_receipt_keeps_real_original_equation425 read m fit
  exact ⟨source,v,e,q,target⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
