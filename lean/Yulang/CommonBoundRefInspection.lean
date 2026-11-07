import Yulang.CommonGeneratedBoundSupport
import Yulang.CommonGeneratedBoundWidth
import Yulang.PresenceGeneratedChildGrammar

/-!
# Inspection directly on fixed symbolic bound references

An original lower node or the synthetic top node supplies the source layer.
Original upper nodes and the dedicated width/required/optional/top bounds
supply targets. The ordinary child IDs and arrow row annotations are retained.

One static simplification is essential for polarity closure: an original
required source has a synthetic width tail. Comparing that tail with a
different required or optional label is always false. Such a whole branch is
removed here, together with literal-false branches; no auxiliary width
source is added to the working grammar.
The earlier generic inspectors and their statements are unchanged.
-/

namespace Yulang.CommonBoundRefInspection

open Common (Ty Row Subtype Equivalent)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonSymbolicBoundInspection
open CommonSymbolicBoundSupport
open CommonGeneratedBoundInspection (PoolSource PoolRigid PoolOutput)
open CommonSymbolicConstraints (Check Branch Alternatives)
open CommonOptionalPoolQueries (queries)

variable {m : Nat}

abbrev Ref (pool : Pool m) := BoundRef (Fin pool.size)
abbrev InputCheck (pool : Pool m) := Check (RowTerm (Fin m)) (Fin pool.size) (Ref pool)

def LowerRef (pool : Pool m) : Ref pool → Prop
  | .original index => PresenceGeneratedChildGrammar.lower (pool.termAt index) = true
  | .top => True
  | _ => False

def PayloadUpper (pool : Pool m) : Option (Fin pool.size) → Prop
  | none => True
  | some index => PresenceGeneratedChildGrammar.upper (pool.termAt index) = true

def UpperRef (pool : Pool m) : Ref pool → Prop
  | .original index => PresenceGeneratedChildGrammar.upper (pool.termAt index) = true
  | .top | .width => True
  | .required label payload | .optional label payload =>
      (label, payload) ∈ queries pool ∧ PayloadUpper pool payload
  | _ => False

def sourceLayer (pool : Pool m) : Ref pool → Option (PoolSource pool)
  | .original index => CommonGeneratedBoundInspection.ofNode pool (pool.termAt index) (pool.at_mem index)
  | .top => some (.rigid .top)
  | _ => none

def dispatchOriginal (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool) : PoolOutput pool :=
  match target with
  | .var _ => [[edge sourceRef targetRef]]
  | .emptyRecord => inspectWidth source
  | .required label payload => inspectRequired source label
      (some (pool.child _ member payload (by simp [subterms])))
  | .base scalar => inspectRigid source (.base scalar) targetRef
  | .pair first last => inspectRigid source
      (.pair (.original (pool.child _ member first (by simp [subterms])))
        (.original (pool.child _ member last (by simp [subterms])))) targetRef
  | .arrow input incoming output outgoing => inspectRigid source
      (.arrow (.original (pool.child _ member input (by simp [subterms]))) incoming
        (.original (pool.child _ member output (by simp [subterms]))) outgoing) targetRef
  | _ => []

def dispatch (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool) : Ref pool → PoolOutput pool
  | .original index => dispatchOriginal pool sourceRef source (pool.termAt index) (pool.at_mem index) (.original index)
  | .top => [[]]
  | .width => inspectWidth source
  | .required label payload => inspectRequired source label payload
  | .optional label payload => inspectOptional source label payload
  | .exactEmpty => []

def rawInspect (pool : Pool m) (source target : Ref pool) : PoolOutput pool :=
  match sourceLayer pool source with
  | none => []
  | some layer => dispatch pool source layer target

/-- Universally false width-source comparisons and literal-false checks. -/
def blocked : InputCheck pool → Bool
  | .childBelow (.ref .width) (.ref (.required _ _)) => true
  | .childBelow (.ref .width) (.ref (.optional _ _)) => true
  | .flag (.literal false) => true
  | _ => false

def prune (output : PoolOutput pool) : PoolOutput pool :=
  output.filter (fun branch => branch.all (fun check => !blocked check))

def inspect (pool : Pool m) (source target : Ref pool) : PoolOutput pool :=
  prune (rawInspect pool source target)

theorem mem_prune (output : PoolOutput pool) (branch : List (InputCheck pool))
    (member : branch ∈ prune output) : branch ∈ output := (List.mem_filter.mp member).1

theorem prune_unblocked (output : PoolOutput pool) (branch : List (InputCheck pool))
    (member : branch ∈ prune output) (check : InputCheck pool) (included : check ∈ branch) :
    blocked check = false := by
  have accepted := List.all_eq_true.mp (List.mem_filter.mp member).2 check included
  cases value : blocked check <;> simp_all

theorem prune_no_false (output : PoolOutput pool) (branch : List (InputCheck pool))
    (member : branch ∈ prune output) : Check.flag (.literal false) ∉ branch := by
  intro included
  have impossible := prune_unblocked output branch member _ included
  cases impossible

theorem prune_no_width_required (output : PoolOutput pool) (branch : List (InputCheck pool))
    (member : branch ∈ prune output) (label : Nat) (payload : Option (Fin pool.size)) :
    edge .width (.required label payload) ∉ branch := by
  intro included
  have impossible := prune_unblocked output branch member _ included
  cases impossible

theorem prune_no_width_optional (output : PoolOutput pool) (branch : List (InputCheck pool))
    (member : branch ∈ prune output) (label : Nat) (payload : Option (Fin pool.size)) :
    edge .width (.optional label payload) ∉ branch := by
  intro included
  have impossible := prune_unblocked output branch member _ included
  cases impossible

theorem inspected_literal_true (pool : Pool m) (source target : Ref pool)
    (branch : List (InputCheck pool)) (returned : branch ∈ inspect pool source target)
    (value : Bool) (included : Check.flag (.literal value) ∈ branch) : value = true := by
  cases value with
  | false => exact False.elim (prune_no_false _ _ returned included)
  | true => rfl

theorem blocked_false (pool : Pool m) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (check : InputCheck pool) (dead : blocked check = true) :
    ¬ check.Holds (CommonPresenceConstraintGraph.rowEval rows) values (BoundRef.eval values) := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target <;> simp only [blocked, Bool.false_eq_true] at dead
      case ref.ref first last =>
        cases first <;> cases last <;> simp only [Bool.false_eq_true] at dead
        case width.required label payload =>
          change ¬ Subtype Common.emptyRecord (Common.required label (payloadValue values payload))
          rw [CommonRecordTargetProfiles.subtype_required_iff]
          exact id
        case width.optional label payload =>
          exact CommonOptionalInspection.width_not_below label (payloadValue values payload)
  | flag expression =>
      cases expression <;> simp only [blocked, Bool.false_eq_true] at dead
      case literal value =>
        cases value <;> simp only [Bool.false_eq_true] at dead
        intro accepted
        cases accepted
  | rowBelow | profileBelow => cases dead

theorem prune_exact (pool : Pool m) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (output : PoolOutput pool) :
    Holds (CommonPresenceConstraintGraph.rowEval rows) values (prune output) ↔
      Holds (CommonPresenceConstraintGraph.rowEval rows) values output := by
  constructor
  · rintro ⟨branch, member, accepted⟩
    exact ⟨branch, mem_prune output branch member, accepted⟩
  · rintro ⟨branch, member, accepted⟩
    refine ⟨branch, List.mem_filter.mpr ⟨member, ?_⟩, accepted⟩
    apply List.all_eq_true.mpr
    intro check included
    cases dead : blocked check with
    | false => rfl
    | true => exact False.elim (blocked_false pool rows values check dead (accepted check included))

theorem lower_supported (pool : Pool m) (reference : Ref pool) (good : LowerRef pool reference) :
    Supported (queries pool) reference := by
  cases reference <;> first | trivial | cases good

theorem upper_supported (pool : Pool m) (reference : Ref pool) (good : UpperRef pool reference) :
    Supported (queries pool) reference := by
  cases reference <;> first | trivial | exact good.1 | cases good

theorem sourceLayer_some (pool : Pool m) (reference : Ref pool) (good : LowerRef pool reference) :
    ∃ source, sourceLayer pool reference = some source := by
  cases reference with
  | original index =>
      exact CommonGeneratedBoundInspection.ofNode_some pool (pool.termAt index) (pool.at_mem index)
        (PresenceGeneratedChildGrammar.lower_head _ good)
  | top => exact ⟨_, rfl⟩
  | _ => cases good

theorem sourceLayer_supported (pool : Pool m) (reference : Ref pool) (source : PoolSource pool)
    (found : sourceLayer pool reference = some source) : SourceSupported (queries pool) source := by
  cases reference with
  | original index => exact CommonGeneratedBoundSupport.ofNode_supported pool (queries pool) _ _ source found
  | top => cases found; trivial
  | _ => cases found

theorem dispatchOriginal_supported (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (sourceSupported : SourceSupported (queries pool) source)
    (referenceSupported : Supported (queries pool) sourceRef)
    (targetSupported : Supported (queries pool) targetRef) :
    OutputSupported (queries pool) (dispatchOriginal pool sourceRef source target member targetRef) := by
  cases target with
  | var => simp [dispatchOriginal, OutputSupported, BranchSupported, edge, referenceSupported, targetSupported]
  | emptyRecord => exact inspect_width_supported _ _ sourceSupported
  | required label payload =>
      exact inspect_required_supported _ (CommonGeneratedBoundSupport.queries_top_closed pool) _ _ _
        sourceSupported (CommonOptionalPoolQueries.required_query pool label payload member)
  | base | pair | arrow => apply inspect_rigid_supported <;> first | assumption | simp
  | _ => simp [dispatchOriginal, OutputSupported]

theorem dispatch_supported (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : Ref pool) (sourceSupported : SourceSupported (queries pool) source)
    (referenceSupported : Supported (queries pool) sourceRef) (targetSupported : Supported (queries pool) target) :
    OutputSupported (queries pool) (dispatch pool sourceRef source target) := by
  cases target with
  | original index => exact dispatchOriginal_supported _ _ _ _ _ _ sourceSupported referenceSupported targetSupported
  | top | exactEmpty => simp [dispatch, OutputSupported, BranchSupported]
  | width => exact inspect_width_supported _ _ sourceSupported
  | required label payload =>
      exact inspect_required_supported _ (CommonGeneratedBoundSupport.queries_top_closed pool)
        _ _ _ sourceSupported targetSupported
  | optional label payload =>
      exact inspect_optional_supported _ (CommonGeneratedBoundSupport.queries_top_closed pool)
        _ _ _ sourceSupported targetSupported

theorem inspect_supported_refs (pool : Pool m) (source target : Ref pool)
    (first : Supported (queries pool) source) (last : Supported (queries pool) target) :
    OutputSupported (queries pool) (inspect pool source target) := by
  intro branch member
  have original := mem_prune (rawInspect pool source target) branch member
  cases found : sourceLayer pool source with
  | none => simp [rawInspect, found] at original
  | some layer =>
      exact dispatch_supported pool source layer target (sourceLayer_supported pool source layer found)
        first last branch (by simpa only [rawInspect, found] using original)

theorem inspect_supported (pool : Pool m) (source target : Ref pool)
    (first : LowerRef pool source) (last : UpperRef pool target) :
    OutputSupported (queries pool) (inspect pool source target) := by
  obtain ⟨layer, found⟩ := sourceLayer_some pool source first
  have supported := dispatch_supported pool source layer target (sourceLayer_supported pool source layer found)
    (lower_supported pool source first) (upper_supported pool target last)
  intro branch member
  apply supported branch
  simpa only [rawInspect, found] using mem_prune (rawInspect pool source target) branch member

end Yulang.CommonBoundRefInspection
