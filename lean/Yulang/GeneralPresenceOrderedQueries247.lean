import Yulang.GeneralPresenceOrderedRebase247
/-! Explicit private-query transport for ordered rebase. All listed observations
are preserved under type equivalence and exact row equality. No claim is made
that actual source/cache/inspector fields have been exhaustively enumerated. -/
namespace Yulang.GeneralPresenceOrderedQueries247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247 GeneralPresenceOrderedSubstitution247
open GeneralPresenceOrderedDependence247 GeneralPresenceOrderedRebase247
open GeneralPresenceModelCongruence245
variable {Name Tag : Type} [DecidableEq Name]

def querySubst (entries : List (Entry Name)) (query : CompTerm Name) : CompTerm Name :=
 ⟨query.ty.subst (mapping entries),query.row.subst (mapping entries)⟩

def ValueEq (model : Model) (first last : Comp model) : Prop :=
 Equiv model first.1 last.1 ∧ first.2 = last.2

theorem query_exact (entries : List (Entry Name)) (query : CompTerm Name)
 (model : Model) (assignment : Name → Comp model) :
 (querySubst entries query).eval model assignment = query.eval model (solve model entries assignment) := by
 have same : (fun name => (mapping entries name).eval model assignment) = solve model entries assignment :=
   funext (mapping_eval entries model assignment)
 simp only [CompTerm.eval] at same
 simp only [querySubst,CompTerm.eval,TyTerm.eval_subst,RowTerm.eval_subst,same]

theorem query_forward (old fresh : List (Entry Name)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (model : Model) (laws : Laws model)
 (assignment : Name → Comp model) (valid : All model assignment (block old)) (query : CompTerm Name) :
 ValueEq model ((querySubst old query).eval model (solve model fresh assignment)) (query.eval model assignment) := by
 rw [query_exact,solve_absorbs model old fresh safe within]
 have compatible := GeneralPresenceOrderedRecovery247.solve_compatible model laws old assignment valid
 exact ⟨type_eval_equiv model laws _ _ compatible query.ty,
   row_eval_equal model _ _ (fun name => (compatible name).2) query.row⟩

def bundleSubst (entries : List (Entry Name)) (bundle : List (Tag × CompTerm Name)) : List (Tag × CompTerm Name) :=
 bundle.map (fun item => (item.1,querySubst entries item.2))

def Stable (model : Model) (observe : Tag → Comp model → Prop) : Prop :=
 ∀ tag first last, ValueEq model first last → (observe tag first ↔ observe tag last)

def Observes (model : Model) (observe : Tag → Comp model → Prop)
 (bundle : List (Tag × CompTerm Name)) (assignment : Name → Comp model) : Prop :=
 ∀ item ∈ bundle, observe item.1 (item.2.eval model assignment)

theorem bundle_exact (entries : List (Entry Name)) (bundle : List (Tag × CompTerm Name))
 (model : Model) (observe : Tag → Comp model → Prop) (assignment : Name → Comp model) :
 Observes model observe (bundleSubst entries bundle) assignment ↔
 Observes model observe bundle (solve model entries assignment) := by
 simp only [Observes,bundleSubst,List.forall_mem_map,query_exact]

theorem bundle_forward (old fresh : List (Entry Name)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (model : Model) (laws : Laws model)
 (observe : Tag → Comp model → Prop) (stable : Stable model observe)
 (assignment : Name → Comp model) (valid : All model assignment (block old))
 (bundle : List (Tag × CompTerm Name)) :
 Observes model observe (bundleSubst old bundle) (solve model fresh assignment) ↔
 Observes model observe bundle assignment := by
 simp only [Observes,bundleSubst,List.forall_mem_map]
 apply forall_congr'
 intro item
 apply forall_congr'
 intro _
 exact stable item.1 _ _ (query_forward old fresh safe within model laws assignment valid item.2)

theorem bundle_tags (entries : List (Entry Name)) (bundle : List (Tag × CompTerm Name)) :
 (bundleSubst entries bundle).map Prod.fst = bundle.map Prod.fst := by
 simp only [bundleSubst,List.map_map,Function.comp_def]

theorem observed_public_models_iff (model : Model) (laws : Laws model)
 (old fresh : List (Entry Name)) (oldSafe : SafeOrder old) (freshSafe : SafeOrder fresh)
 (within : TargetsWithin fresh old) (consumers : List (Atom Name))
 (bundle : List (Tag × CompTerm Name)) (observe : Tag → Comp model → Prop) (stable : Stable model observe)
 (sharedNames : Name → Prop)
 (privateTargets : ∀ name, sharedNames name → ∀ entry ∈ old, entry.1 ≠ name)
 (boundary : Name → Comp model) :
 (∃ assignment, All model assignment (consumers ++ block old) ∧
   Agrees model sharedNames assignment boundary ∧ Observes model observe bundle assignment) ↔
 (∃ assignment, All model assignment (rewrite old consumers ++ block fresh) ∧
   Agrees model sharedNames assignment boundary ∧ Observes model observe (bundleSubst old bundle) assignment) := by
 constructor
 · rintro ⟨assignment,valid,agree,observed⟩
   refine ⟨solve model fresh assignment,models_forward model laws old fresh oldSafe freshSafe within consumers assignment valid,?_,?_⟩
   · intro name shared
     rw [solve_outside model fresh assignment name]
     · exact agree name shared
     · intro entry member
       obtain ⟨original,present,equal⟩ := within entry member
       rw [← equal]
       exact privateTargets name shared original present
   · exact (bundle_forward old fresh oldSafe within model laws observe stable assignment
       ((all_append model assignment consumers (block old)).mp valid).2 bundle).mpr observed
 · rintro ⟨assignment,valid,agree,observed⟩
   refine ⟨solve model old assignment,models_backward model laws old fresh oldSafe consumers assignment valid,?_,?_⟩
   · intro name shared
     rw [solve_outside model old assignment name (privateTargets name shared)]
     exact agree name shared
   · exact (bundle_exact old bundle model observe assignment).mp observed

def Probe (value : CommonNominalFullCarrier.Ty) (depth rank : Nat)
 (environment : CommonNominalFullDemand.Environment Common.Row)
 (observation : CommonNominalFullDemand.Observation Common.Row) : Prop :=
 CommonNominalFullDemand.ProbeAt Common.rowLe rank environment
   (CommonNominalFullCarrier.observeTy depth value) observation

theorem common_query_probe (old fresh : List (Entry Name)) (safe : SafeOrder old)
 (within : TargetsWithin fresh old) (assignment : Name → Comp CommonNominalFullCarrier.model)
 (valid : All CommonNominalFullCarrier.model assignment (block old)) (query : CompTerm Name)
 (depth rank : Nat) (environment : CommonNominalFullDemand.Environment Common.Row)
 (observation : CommonNominalFullDemand.Observation Common.Row) :
 Probe ((querySubst old query).eval CommonNominalFullCarrier.model
   (solve CommonNominalFullCarrier.model fresh assignment)).1 depth rank environment observation ↔
 Probe (query.eval CommonNominalFullCarrier.model assignment).1 depth rank environment observation := by
 have same := (query_forward old fresh safe within _ GeneralPresenceCommonLaws245.common_laws assignment valid query).1
 exact (CommonNominalFullDemand.producerEq_iff_probe _ _).mp ⟨same.1 depth,same.2 depth⟩ rank environment observation

end Yulang.GeneralPresenceOrderedQueries247
