import Yulang.GeneralPresenceRebasePlan245
/-! Explicit transport of type/row query payloads. This does not claim that
actual inspector, cache or historical-origin records have been enumerated.
An unrewritten query of a replaced private target is not covered. -/
namespace Yulang.GeneralPresenceQueryTransport245
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244 GeneralPresenceOwnerTable244
open GeneralPresenceOwnerOwnership244 GeneralPresenceReadback245
open GeneralPresenceModelCongruence245 GeneralPresencePreorderExtension245
open GeneralPresenceModelExtension245 (readback_absorbs)
variable {Name Tag : Type} [DecidableEq Name]

def querySubst (entries : List (Entry Name)) (query : CompTerm Name) : CompTerm Name :=
 ⟨query.ty.subst (substitution entries),query.row.subst (substitution entries)⟩

def ValueEq (model : Model) (first last : Comp model) : Prop :=
 Equiv model first.1 last.1 ∧ first.2 = last.2

theorem query_readback (entries : List (Entry Name)) (model : Model)
 (assignment : Name → Comp model) (query : CompTerm Name) :
 (querySubst entries query).eval model assignment = query.eval model (readback entries model assignment) := by
 simp only [querySubst,CompTerm.eval,TyTerm.eval_subst,RowTerm.eval_subst]
 rfl

theorem query_forward (old fresh : List (Entry Name)) (external : External old)
 (coherent : Coherent old) (within : TargetsWithin fresh old)
 (model : Model) (laws : Laws model) (assignment : Name → Comp model)
 (valid : PresenceNormalForm.All model assignment (block old)) (query : CompTerm Name) :
 ValueEq model ((querySubst old query).eval model (readback fresh model assignment))
   (query.eval model assignment) := by
 rw [query_readback,readback_absorbs old fresh external coherent within]
 have compatible := readback_compatible old model laws assignment valid
 exact ⟨type_eval_equiv model laws _ _ compatible query.ty,
   row_eval_equal model _ _ (fun name => (compatible name).2) query.row⟩

def bundleSubst (entries : List (Entry Name)) (bundle : List (Tag × CompTerm Name)) : List (Tag × CompTerm Name) :=
 bundle.map (fun item => (item.1,querySubst entries item.2))

theorem bundle_tags (entries : List (Entry Name)) (bundle : List (Tag × CompTerm Name)) :
 (bundleSubst entries bundle).map Prod.fst = bundle.map Prod.fst := by
 simp only [bundleSubst,List.map_map,Function.comp_def]

theorem bundle_length (entries : List (Entry Name)) (bundle : List (Tag × CompTerm Name)) :
 (bundleSubst entries bundle).length = bundle.length := by simp [bundleSubst]

theorem bundle_forward (old fresh : List (Entry Name)) (external : External old)
 (coherent : Coherent old) (within : TargetsWithin fresh old)
 (model : Model) (laws : Laws model) (assignment : Name → Comp model)
 (valid : PresenceNormalForm.All model assignment (block old)) (bundle : List (Tag × CompTerm Name)) :
 ∀ item ∈ bundleSubst old bundle, ∃ original ∈ bundle,
 item.1 = original.1 ∧ ValueEq model (item.2.eval model (readback fresh model assignment)) (original.2.eval model assignment) := by
 intro item member
 obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
 exact ⟨original,present,rfl,query_forward old fresh external coherent within model laws assignment valid original.2⟩

def Probe (value : CommonNominalFullCarrier.Ty) (depth rank : Nat)
 (environment : CommonNominalFullDemand.Environment Common.Row)
 (observation : CommonNominalFullDemand.Observation Common.Row) : Prop :=
 CommonNominalFullDemand.ProbeAt Common.rowLe rank environment
   (CommonNominalFullCarrier.observeTy depth value) observation

/-- All-depth, all-negative-rank concrete observations of a transported query
are preserved, rather than only its public free-variable values. -/
theorem common_query_probe (old fresh : List (Entry Name)) (external : External old)
 (coherent : Coherent old) (within : TargetsWithin fresh old)
 (assignment : Name → Comp CommonNominalFullCarrier.model)
 (valid : PresenceNormalForm.All CommonNominalFullCarrier.model assignment (block old))
 (query : CompTerm Name) (depth rank : Nat)
 (environment : CommonNominalFullDemand.Environment Common.Row)
 (observation : CommonNominalFullDemand.Observation Common.Row) :
 Probe ((querySubst old query).eval CommonNominalFullCarrier.model
   (readback fresh CommonNominalFullCarrier.model assignment)).1 depth rank environment observation ↔
 Probe (query.eval CommonNominalFullCarrier.model assignment).1 depth rank environment observation := by
 have same := (query_forward old fresh external coherent within _ GeneralPresenceCommonLaws245.common_laws assignment valid query).1
 exact (CommonNominalFullDemand.producerEq_iff_probe _ _).mp ⟨same.1 depth,same.2 depth⟩ rank environment observation
end Yulang.GeneralPresenceQueryTransport245
