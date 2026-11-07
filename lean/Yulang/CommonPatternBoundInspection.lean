import Yulang.CommonBoundRefExact

/-!
# Pattern upper bounds in the finite Common inspector

Pattern checking adds root variant and dedicated optional-union targets to
the historical source upper grammar. Their payload references remain shared
original nodes. The local exactness theorem below is consumed by the separate
CommonPatternBoundWorklist module; solved families have their own obligations.
-/

namespace Yulang.CommonPatternBoundInspection

open Common (Ty Row Equivalent Subtype)
open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonSymbolicBoundInspection
open CommonGeneratedBoundInspection (PoolSource PoolOutput)
open CommonPresenceConstraintGraph (rowEval lowerNode)
open CommonBoundRefInspection (Ref)

variable {m : Nat}

inductive Upper : TyTerm α → Prop where
  | old : PresenceGeneratedChildGrammar.upper type = true → Upper type
  | variant : PresenceGeneratedChildGrammar.upper payload = true → Upper (.variant tag payload)
  | optional : PresenceGeneratedChildGrammar.upper payload = true →
      Upper (.union .exactEmpty (.required label payload))

def dispatchOriginal (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool) : PoolOutput pool :=
  match target with
  | .variant tag payload =>
      inspectRigid source (.variant tag (.original (pool.child _ member payload (by simp [subterms])))) targetRef
  | .union .exactEmpty (.required label payload) =>
      inspectOptional source label (some (pool.child _ member payload (by simp [subterms])))
  | target => CommonBoundRefInspection.dispatchOriginal pool sourceRef source target member targetRef

theorem dispatchOriginal_old (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (good : PresenceGeneratedChildGrammar.upper target = true) :
    dispatchOriginal pool sourceRef source target member targetRef =
      CommonBoundRefInspection.dispatchOriginal pool sourceRef source target member targetRef := by
  cases target <;> first | rfl | cases good

/-- Exact at arbitrary original Common constructor realizers, including all
regular assigned payloads and rows. The local source-width condition is the
same record/default-tail condition used by the historical optional inspector. -/
theorem dispatchOriginal_exact (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (targetGood : Upper target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (targetSame : Equivalent ((lowerNode pool target member).eval rows values) (targetRef.eval values))
    (sourceWidth : LocalWidth values source) :
    Holds (rowEval rows) values (dispatchOriginal pool sourceRef source target member targetRef) ↔
      Subtype (sourceRef.eval values) (targetRef.eval values) := by
  cases targetGood with
  | old good =>
      rw [dispatchOriginal_old pool sourceRef source target member targetRef good]
      exact CommonBoundRefInspection.dispatchOriginal_exact pool sourceRef source target member targetRef
        good rows values sourceSame targetSame
  | variant good =>
      exact (inspect_rigid_exact (rowEval rows) values source
        (.variant _ (.original (pool.child _ member _ (by simp [subterms])))) targetRef targetSame).trans
        (subtype_congr sourceSame targetSame)
  | @optional payload label good =>
      have empty := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes .exactEmpty
        (pool.closed _ member _ (by simp [subterms]))
      have required := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes
        (.required label payload) (pool.closed _ member _ (by simp [subterms]))
      have targetLayer : Equivalent
          ((BoundRef.optional label (some (pool.child _ member payload (by simp [subterms])))).eval values)
          ((lowerNode pool _ member).eval rows values) :=
        ⟨Common.common_union_mono empty.1 required.1, Common.common_union_mono empty.2 required.2⟩
      exact (inspect_optional_exact (rowEval rows) values source _
        (some (pool.child _ member _ (by simp [subterms]))) sourceWidth).trans
        (subtype_congr sourceSame (Common.equivalent_trans targetLayer targetSame))

def UpperRef (pool : Pool m) : Ref pool → Prop
  | .original index => Upper (pool.termAt index)
  | target => CommonBoundRefInspection.UpperRef pool target

def dispatch (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool) : Ref pool → PoolOutput pool
  | .original index => dispatchOriginal pool sourceRef source (pool.termAt index) (pool.at_mem index) (.original index)
  | target => CommonBoundRefInspection.dispatch pool sourceRef source target

theorem dispatch_exact (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : Ref pool) (targetGood : UpperRef pool target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (sourceWidth : LocalWidth values source) :
    Holds (rowEval rows) values (dispatch pool sourceRef source target) ↔
      Subtype (sourceRef.eval values) (target.eval values) := by
  cases target with
  | original index =>
      exact dispatchOriginal_exact pool sourceRef source (pool.termAt index) (pool.at_mem index)
        (.original index) targetGood rows values realizes sourceSame (realizes index) sourceWidth
  | _ =>
      simp only [dispatch]
      apply CommonBoundRefInspection.dispatch_exact pool sourceRef source
      · exact targetGood
      · exact realizes
      · exact sourceSame
      · exact sourceWidth

open CommonSymbolicBoundSupport
open CommonOptionalPoolQueries (queries)

theorem dispatchOriginal_supported (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (sourceSupported : SourceSupported (queries pool) source)
    (referenceSupported : Supported (queries pool) sourceRef)
    (targetSupported : Supported (queries pool) targetRef) :
    OutputSupported (queries pool) (dispatchOriginal pool sourceRef source target member targetRef) := by
  unfold dispatchOriginal
  split
  · apply inspect_rigid_supported <;> first | assumption | simp
  · rename_i original originalMember label payload targetMember
    have requiredMember : .required label payload ∈ pool.terms :=
      pool.closed _ targetMember _ (by simp [subterms])
    exact inspect_optional_supported _ (CommonGeneratedBoundSupport.queries_top_closed pool) _ _ _
      sourceSupported (CommonOptionalPoolQueries.required_query pool label payload requiredMember)
  · exact CommonBoundRefInspection.dispatchOriginal_supported pool sourceRef source _ _ targetRef
      sourceSupported referenceSupported targetSupported

theorem dispatch_supported (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : Ref pool) (sourceSupported : SourceSupported (queries pool) source)
    (referenceSupported : Supported (queries pool) sourceRef) (targetSupported : Supported (queries pool) target) :
    OutputSupported (queries pool) (dispatch pool sourceRef source target) := by
  cases target with
  | original index =>
      exact dispatchOriginal_supported pool sourceRef source _ _ _
        sourceSupported referenceSupported targetSupported
  | _ =>
      simp only [dispatch]
      apply CommonBoundRefInspection.dispatch_supported pool sourceRef source
      · exact sourceSupported
      · exact referenceSupported
      · exact targetSupported

def inspect (pool : Pool m) (source target : Ref pool) : PoolOutput pool :=
  CommonBoundRefInspection.prune <|
    match CommonBoundRefInspection.sourceLayer pool source with
    | none => []
    | some layer => dispatch pool source layer target

theorem inspect_supported_refs (pool : Pool m) (source target : Ref pool)
    (first : Supported (queries pool) source) (last : Supported (queries pool) target) :
    OutputSupported (queries pool) (inspect pool source target) := by
  intro branch member
  have original := CommonBoundRefInspection.mem_prune _ branch member
  cases found : CommonBoundRefInspection.sourceLayer pool source with
  | none => simp [found] at original
  | some layer =>
    exact dispatch_supported pool source layer target
      (CommonBoundRefInspection.sourceLayer_supported pool source layer found) first last branch
      (by simpa only [found] using original)

theorem inspect_exact (pool : Pool m) (source target : Ref pool)
    (first : CommonBoundRefInspection.LowerRef pool source) (last : UpperRef pool target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values)
    (widths : CommonGeneratedWidth.PoolWidth pool values) :
    Holds (rowEval rows) values (inspect pool source target) ↔
      Subtype (source.eval values) (target.eval values) := by
  obtain ⟨layer, found⟩ := CommonBoundRefInspection.sourceLayer_some pool source first
  rw [inspect, CommonBoundRefInspection.prune_exact, found]
  exact dispatch_exact pool source layer target last rows values realizes
    (CommonBoundRefInspection.sourceLayer_exact pool source layer found rows values realizes)
    (CommonBoundRefInspection.sourceLayer_width pool source layer first found values widths)

end Yulang.CommonPatternBoundInspection
