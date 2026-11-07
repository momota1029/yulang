import Yulang.CommonBoundRefInspection
import Yulang.CommonOptionalPoolRows
import Yulang.CommonSymbolicRowConstraints

/-!
# Row support of every fixed bound-reference inspection branch

Only a comparison between two original arrow heads emits row checks. Every
other dispatcher case emits type edges or literal flags. Thus simple rows
throughout the original pool suffice for every pair of bound references,
even without lower/upper polarity or query-support premises.

All actual source and Core clauses supply this syntactic row invariant
internally. Optional pool extension preserves it as well. The statements do
not quantify a semantic assignment, invoke a row solver or assume that any
returned check holds.
-/

namespace Yulang.CommonBoundRefRows

open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (splitAtoms)
open CommonGeneratedPoolRows (AllSimpleRows)
open CommonSymbolicBoundInspection
open CommonGeneratedBoundInspection (PoolSource PoolOutput)
open CommonBoundRefInspection (Ref InputCheck sourceLayer dispatchOriginal dispatch rawInspect inspect mem_prune)
open CommonSymbolicRowConstraints (AllRows CheckRows NodeRows)
open PresenceSourceConstraintSupport (simpleRow simpleTyRows)

variable {m : Nat}

def SourceRows (property : Rows → Prop) : Source Rows Node → Prop
  | .rigid node => NodeRows property node
  | _ => True

def OutputRows (property : Rows → Prop) (output : Output Rows Node) : Prop :=
  ∀ branch ∈ output, AllRows property branch

theorem required_rows (property : Rows → Prop) (source : Source Rows Node)
    (label : Nat) (payload : Option Node) : OutputRows property (inspectRequired source label payload) := by
  cases source with
  | record current head tail | recordDefault current head tail =>
      by_cases same : label = current <;>
        simp [inspectRequired, same, defaultBranches, edge, OutputRows, AllRows, CheckRows]
  | rigid node =>
      cases node <;> simp [inspectRequired, OutputRows, AllRows, CheckRows]
  | _ => simp [inspectRequired, edge, OutputRows, AllRows, CheckRows]

theorem optional_rows (property : Rows → Prop) (source : Source Rows Node)
    (label : Nat) (payload : Option Node) : OutputRows property (inspectOptional source label payload) := by
  cases source with
  | record current head tail | recordDefault current head tail =>
      by_cases same : label = current <;>
        simp [inspectOptional, same, defaultBranches, edge, OutputRows, AllRows, CheckRows]
  | rigid node =>
      cases node <;> simp [inspectOptional, OutputRows, AllRows, CheckRows]
  | _ => simp [inspectOptional, edge, OutputRows, AllRows, CheckRows]

theorem width_rows (property : Rows → Prop) (source : Source Rows Node) :
    OutputRows property (inspectWidth source) := by
  cases source with
  | rigid node => cases node <;> simp [inspectWidth, OutputRows, AllRows, CheckRows]
  | _ => simp [inspectWidth, edge, OutputRows, AllRows, CheckRows]

theorem rigid_rows (property : Rows → Prop) (source : Source Rows Node)
    (target : Rigid Rows Node) (targetRef : BoundRef Node)
    (first : SourceRows property source) (last : NodeRows property target) :
    OutputRows property (inspectRigid source target targetRef) := by
  cases source with
  | reference | union => simp [inspectRigid, edge, OutputRows, AllRows, CheckRows]
  | rigid node =>
      intro branch member
      have same := List.mem_singleton.mp member
      subst branch
      exact CommonSymbolicRowConstraints.inspect_preserves_rows property node target first last
  | width | exactEmpty | record | recordDefault =>
      cases target <;> simp [inspectRigid, OutputRows, AllRows]

theorem ofNode_rows (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (source : PoolSource pool) (found : CommonGeneratedBoundInspection.ofNode pool term member = some source)
    (good : simpleTyRows term = true) : SourceRows (fun row => simpleRow row = true) source := by
  cases term with
  | arrow input incoming output outgoing =>
      simp only [CommonGeneratedBoundInspection.ofNode] at found
      cases found
      have parts : ((simpleTyRows input = true ∧ simpleRow incoming = true) ∧
          simpleTyRows output = true) ∧ simpleRow outgoing = true := by
        simpa only [simpleTyRows, Bool.and_eq_true] using good
      exact ⟨parts.1.1.2, parts.2⟩
  | _ => simp only [CommonGeneratedBoundInspection.ofNode] at found; cases found <;> trivial

theorem sourceLayer_rows (pool : Pool m) (good : AllSimpleRows pool) (reference : Ref pool)
    (source : PoolSource pool) (found : sourceLayer pool reference = some source) :
    SourceRows (fun row => simpleRow row = true) source := by
  cases reference with
  | original index => exact ofNode_rows pool _ _ source found (good index)
  | top => cases found; trivial
  | _ => cases found

theorem dispatchOriginal_rows (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (first : SourceRows (fun row => simpleRow row = true) source) (last : simpleTyRows target = true) :
    OutputRows (fun row => simpleRow row = true)
      (dispatchOriginal pool sourceRef source target member targetRef) := by
  cases target with
  | var => simp [dispatchOriginal, edge, OutputRows, AllRows, CheckRows]
  | emptyRecord => exact width_rows _ source
  | required label payload => exact required_rows _ source label _
  | base | pair => exact rigid_rows _ source _ targetRef first trivial
  | arrow input incoming output outgoing =>
      apply rigid_rows _ source _ targetRef first
      have parts : ((simpleTyRows input = true ∧ simpleRow incoming = true) ∧
          simpleTyRows output = true) ∧ simpleRow outgoing = true := by
        simpa only [simpleTyRows, Bool.and_eq_true] using last
      exact ⟨parts.1.1.2, parts.2⟩
  | _ => simp [dispatchOriginal, OutputRows]

theorem dispatch_rows (pool : Pool m) (good : AllSimpleRows pool)
    (sourceRef : Ref pool) (source : PoolSource pool) (target : Ref pool)
    (first : SourceRows (fun row => simpleRow row = true) source) :
    OutputRows (fun row => simpleRow row = true) (dispatch pool sourceRef source target) := by
  cases target with
  | original index => exact dispatchOriginal_rows pool sourceRef source _ _ _ first (good index)
  | top | exactEmpty => simp [dispatch, OutputRows, AllRows]
  | width => exact width_rows _ source
  | required label payload => exact required_rows _ source label payload
  | optional label payload => exact optional_rows _ source label payload

theorem rawInspect_rows (pool : Pool m) (good : AllSimpleRows pool) (source target : Ref pool) :
    OutputRows (fun row => simpleRow row = true) (rawInspect pool source target) := by
  cases found : sourceLayer pool source with
  | none => simp [rawInspect, found, OutputRows]
  | some layer =>
      simpa only [rawInspect, found] using
        dispatch_rows pool good source layer target (sourceLayer_rows pool good source layer found)

/-- Every raw bound-reference pair is allowed. No polarity, support or
meaning premise is needed to preserve row syntax. -/
theorem inspect_rows (pool : Pool m) (good : AllSimpleRows pool) (source target : Ref pool)
    (branch : List (InputCheck pool)) (returned : branch ∈ inspect pool source target) :
    AllRows (fun row => simpleRow row = true) branch :=
  rawInspect_rows pool good source target branch (mem_prune _ branch returned)

theorem generated_inspection_rows (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (source target : Ref (splitAtoms clause.pack).pool)
    (branch : List (InputCheck (splitAtoms clause.pack).pool))
    (returned : branch ∈ inspect (splitAtoms clause.pack).pool source target) :
    AllRows (fun row => simpleRow row = true) branch :=
  inspect_rows _ (CommonGeneratedPoolRows.generated_pool_rows expression clause generated)
    source target branch returned

theorem generated_core_inspection_rows (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (source target : Ref (splitAtoms clause.pack).pool)
    (branch : List (InputCheck (splitAtoms clause.pack).pool))
    (returned : branch ∈ inspect (splitAtoms clause.pack).pool source target) :
    AllRows (fun row => simpleRow row = true) branch :=
  inspect_rows _ (CommonGeneratedPoolRows.generated_core_pool_rows expression clause generated)
    source target branch returned

theorem generated_emitted_rows_supported (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (source target : Ref (splitAtoms clause.pack).pool)
    (branch : List (InputCheck (splitAtoms clause.pack).pool))
    (returned : branch ∈ inspect (splitAtoms clause.pack).pool source target) :
    RowFlowSchemes.supported (CommonSymbolicRowConstraints.emittedRows branch) = true :=
  CommonSymbolicRowConstraints.emitted_rows_supported branch
    (generated_inspection_rows expression clause generated source target branch returned)

theorem generated_core_emitted_rows_supported (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (source target : Ref (splitAtoms clause.pack).pool)
    (branch : List (InputCheck (splitAtoms clause.pack).pool))
    (returned : branch ∈ inspect (splitAtoms clause.pack).pool source target) :
    RowFlowSchemes.supported (CommonSymbolicRowConstraints.emittedRows branch) = true :=
  CommonSymbolicRowConstraints.emitted_rows_supported branch
    (generated_core_inspection_rows expression clause generated source target branch returned)

end Yulang.CommonBoundRefRows
