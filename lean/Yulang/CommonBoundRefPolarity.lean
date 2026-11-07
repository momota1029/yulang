import Yulang.CommonBoundRefInspection

/-!
# One-step polarity closure of fixed bound-reference inspection

Original proper children lie in the recursive upper grammar. They may be
used on either side of a child edge, including reversed arrow inputs. New
required and optional references occur only as upper bounds. The one static
width-tail exception is eliminated by the inspector's proved-false pruning.

These are original-syntax provenance facts; variable assignments remain
arbitrary common regular types. No all-parameter solution family is asserted.
-/

namespace Yulang.CommonBoundRefInspection

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonSymbolicBoundInspection
open CommonGeneratedBoundInspection (PoolSource PoolRigid PoolOutput)
open CommonOptionalPoolQueries (queries)

variable {m : Nat}

def OriginalUpper (pool : Pool m) : Ref pool → Prop
  | .original index => PresenceGeneratedChildGrammar.upper (pool.termAt index) = true
  | _ => False

def TailUpper (pool : Pool m) : Ref pool → Prop
  | .width => True
  | reference => OriginalUpper pool reference

def RigidGrammar (pool : Pool m) : PoolRigid pool → Prop
  | .pair first last | .arrow first _ last _ => OriginalUpper pool first ∧ OriginalUpper pool last
  | .variant _ payload => OriginalUpper pool payload
  | _ => True

def SourceGrammar (pool : Pool m) : PoolSource pool → Prop
  | .reference node => LowerRef pool node
  | .union first last => OriginalUpper pool first ∧ OriginalUpper pool last
  | .rigid node => RigidGrammar pool node
  | .record _ payload tail => OriginalUpper pool payload ∧ TailUpper pool tail
  | .recordDefault _ source fallback => OriginalUpper pool source ∧ OriginalUpper pool fallback
  | _ => True

def PolarCheck (pool : Pool m) : InputCheck pool → Prop
  | .childBelow (.ref source) (.ref target) => LowerRef pool source ∧ UpperRef pool target
  | .rowBelow _ _ | .flag (.literal _) => True
  | _ => False

def WeakCheck (pool : Pool m) (check : InputCheck pool) : Prop :=
  PolarCheck pool check ∨ blocked check = true

def OutputWeak (pool : Pool m) (output : PoolOutput pool) : Prop :=
  ∀ branch ∈ output, ∀ check ∈ branch, WeakCheck pool check

def OutputPolar (pool : Pool m) (output : PoolOutput pool) : Prop :=
  ∀ branch ∈ output, ∀ check ∈ branch, PolarCheck pool check

theorem OriginalUpper.lower (pool : Pool m) (reference : Ref pool) (good : OriginalUpper pool reference) :
    LowerRef pool reference := by
  cases reference with
  | original index => exact PresenceGeneratedChildGrammar.upper_lower _ good
  | _ => cases good

theorem OriginalUpper.upper (pool : Pool m) (reference : Ref pool) (good : OriginalUpper pool reference) :
    UpperRef pool reference := by
  cases reference <;> first | exact good | cases good

theorem payload_upper (pool : Pool m) (payload : Option (Fin pool.size)) (good : PayloadUpper pool payload) :
    UpperRef pool (payloadRef payload) := by
  cases payload <;> first | exact good | trivial

theorem child_original_upper (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (child : TyTerm (Fin m)) (inside : child ∈ subterms term)
    (good : PresenceGeneratedChildGrammar.upper child = true) :
    OriginalUpper pool (.original (pool.child term member child inside)) := by
  simpa only [OriginalUpper, Pool.child, Pool.termAt_reference] using good

theorem ofNode_grammar (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (good : PresenceGeneratedChildGrammar.lower term = true) (source : PoolSource pool)
    (found : CommonGeneratedBoundInspection.ofNode pool term member = some source) :
    SourceGrammar pool source := by
  cases term <;> simp only [CommonGeneratedBoundInspection.ofNode] at found <;> cases found
  all_goals
    simp_all [SourceGrammar, RigidGrammar, OriginalUpper, TailUpper, LowerRef,
      Pool.child, Pool.input, PresenceGeneratedChildGrammar.lower]

theorem sourceLayer_grammar (pool : Pool m) (reference : Ref pool) (good : LowerRef pool reference)
    (source : PoolSource pool) (found : sourceLayer pool reference = some source) :
    SourceGrammar pool source := by
  cases reference with
  | original index => exact ofNode_grammar pool _ _ good source found
  | top => cases found; trivial
  | _ => cases good

theorem prune_polar (pool : Pool m) (output : PoolOutput pool) (weak : OutputWeak pool output) :
    OutputPolar pool (prune output) := by
  intro branch member check included
  have allowed := weak branch (mem_prune output branch member) check included
  rcases allowed with good | dead
  · exact good
  · have alive := prune_unblocked output branch member check included
    rw [alive] at dead
    cases dead

private theorem weak_edge (pool : Pool m) (source target : Ref pool)
    (first : LowerRef pool source) (last : UpperRef pool target) :
    WeakCheck pool (edge source target) := Or.inl ⟨first, last⟩

theorem default_branches_weak (pool : Pool m) (label : Nat) (source fallback : Ref pool)
    (payload : Option (Fin pool.size)) (first : OriginalUpper pool source)
    (last : OriginalUpper pool fallback) (selected : (label, payload) ∈ queries pool)
    (payloadGood : PayloadUpper pool payload) :
    OutputWeak pool (defaultBranches label source fallback payload) := by
  have sourceLower := first.lower pool source
  have fallbackLower := last.lower pool fallback
  have payloadUpper := payload_upper pool payload payloadGood
  have optionalUpper : UpperRef pool (.optional label payload) := ⟨selected, payloadGood⟩
  have topUpper : UpperRef pool (.required label none) :=
    ⟨CommonOptionalPoolQueries.top_query_closed pool (label, payload) selected, trivial⟩
  have topLower : LowerRef pool .top := trivial
  have widthUpper : UpperRef pool .width := trivial
  simp [OutputWeak, WeakCheck, PolarCheck, defaultBranches, edge,
    sourceLower, fallbackLower, payloadUpper, optionalUpper, topUpper, topLower, widthUpper]

private theorem tail_required_weak (pool : Pool m) (tail : Ref pool) (good : TailUpper pool tail)
    (label : Nat) (payload : Option (Fin pool.size)) (targetGood : UpperRef pool (.required label payload)) :
    WeakCheck pool (edge tail (.required label payload)) := by
  cases tail with
  | width => exact Or.inr rfl
  | original index => exact weak_edge pool _ _ (OriginalUpper.lower pool (.original index) good) targetGood
  | _ => cases good

private theorem tail_optional_weak (pool : Pool m) (tail : Ref pool) (good : TailUpper pool tail)
    (label : Nat) (payload : Option (Fin pool.size)) (targetGood : UpperRef pool (.optional label payload)) :
    WeakCheck pool (edge tail (.optional label payload)) := by
  cases tail with
  | width => exact Or.inr rfl
  | original index => exact weak_edge pool _ _ (OriginalUpper.lower pool (.original index) good) targetGood
  | _ => cases good

theorem required_weak (pool : Pool m) (source : PoolSource pool) (good : SourceGrammar pool source)
    (label : Nat) (payload : Option (Fin pool.size)) (targetGood : UpperRef pool (.required label payload)) :
    OutputWeak pool (inspectRequired source label payload) := by
  have payloadGood := payload_upper pool payload targetGood.2
  cases source with
  | reference node =>
      simpa only [inspectRequired, OutputWeak, List.mem_singleton, forall_eq, edge] using
        weak_edge pool node (.required label payload) good targetGood
  | union first last =>
      have left := weak_edge pool first (.required label payload) (good.1.lower pool first) targetGood
      have right := weak_edge pool last (.required label payload) (good.2.lower pool last) targetGood
      simpa [inspectRequired, OutputWeak] using And.intro left right
  | record current head tail =>
      by_cases same : label = current
      · subst current
        have child := weak_edge pool head (payloadRef payload) (good.1.lower pool head) payloadGood
        simpa [inspectRequired, OutputWeak] using child
      · have child := tail_required_weak pool tail good.2 label payload targetGood
        simpa [inspectRequired, same, OutputWeak] using child
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        simpa only [inspectRequired, ↓reduceIte] using
          default_branches_weak pool label base fallback payload good.1 good.2 targetGood.1 targetGood.2
      · have child := weak_edge pool base (.required label payload) (good.1.lower pool base) targetGood
        simpa [inspectRequired, same, OutputWeak] using child
  | width | exactEmpty => simp [inspectRequired, OutputWeak]
  | rigid node => cases node <;> simp [inspectRequired, OutputWeak]

theorem optional_weak (pool : Pool m) (source : PoolSource pool) (good : SourceGrammar pool source)
    (label : Nat) (payload : Option (Fin pool.size)) (targetGood : UpperRef pool (.optional label payload)) :
    OutputWeak pool (inspectOptional source label payload) := by
  have payloadGood := payload_upper pool payload targetGood.2
  cases source with
  | reference node =>
      simpa [inspectOptional, OutputWeak] using weak_edge pool node (.optional label payload) good targetGood
  | union first last =>
      have left := weak_edge pool first (.optional label payload) (good.1.lower pool first) targetGood
      have right := weak_edge pool last (.optional label payload) (good.2.lower pool last) targetGood
      simpa [inspectOptional, OutputWeak] using And.intro left right
  | record current head tail =>
      by_cases same : label = current
      · subst current
        have child := weak_edge pool head (payloadRef payload) (good.1.lower pool head) payloadGood
        simpa [inspectOptional, OutputWeak] using child
      · have child := tail_optional_weak pool tail good.2 label payload targetGood
        simpa [inspectOptional, same, OutputWeak] using child
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        simpa only [inspectOptional, ↓reduceIte] using
          default_branches_weak pool label base fallback payload good.1 good.2 targetGood.1 targetGood.2
      · have child := weak_edge pool base (.optional label payload) (good.1.lower pool base) targetGood
        simpa [inspectOptional, same, OutputWeak] using child
  | width | exactEmpty => simp [inspectOptional, OutputWeak]
  | rigid node => cases node <;> simp [inspectOptional, OutputWeak]

theorem width_weak (pool : Pool m) (source : PoolSource pool) (good : SourceGrammar pool source) :
    OutputWeak pool (inspectWidth source) := by
  have widthUpper : UpperRef pool .width := trivial
  cases source with
  | reference node =>
      simpa [inspectWidth, OutputWeak] using weak_edge pool node .width good widthUpper
  | union first last =>
      have left := weak_edge pool first .width (good.1.lower pool first) widthUpper
      have right := weak_edge pool last .width (good.2.lower pool last) widthUpper
      simpa [inspectWidth, OutputWeak] using And.intro left right
  | width | exactEmpty | record | recordDefault => simp [inspectWidth, OutputWeak]
  | rigid node => cases node <;> simp [inspectWidth, OutputWeak]

theorem rigid_weak (pool : Pool m) (source : PoolSource pool) (sourceGood : SourceGrammar pool source)
    (target : PoolRigid pool) (targetGood : RigidGrammar pool target) (targetRef : Ref pool)
    (referenceGood : UpperRef pool targetRef) : OutputWeak pool (inspectRigid source target targetRef) := by
  cases source with
  | reference node =>
      simpa [inspectRigid, OutputWeak] using weak_edge pool node targetRef sourceGood referenceGood
  | union first last =>
      have left := weak_edge pool first targetRef (sourceGood.1.lower pool first) referenceGood
      have right := weak_edge pool last targetRef (sourceGood.2.lower pool last) referenceGood
      simpa [inspectRigid, OutputWeak] using And.intro left right
  | width | exactEmpty | record | recordDefault =>
      cases target <;> simp [inspectRigid, OutputWeak]
  | rigid node =>
      cases node <;> cases target
      all_goals try simp [inspectRigid, CommonSymbolicRigidInspection.inspect, OutputWeak, WeakCheck, PolarCheck]
      case pair.pair first last first' last' =>
        exact ⟨Or.inl ⟨sourceGood.1.lower pool first, targetGood.1.upper pool first'⟩,
          Or.inl ⟨sourceGood.2.lower pool last, targetGood.2.upper pool last'⟩⟩
      case variant.variant label payload label' payload' =>
        exact Or.inl ⟨OriginalUpper.lower pool payload sourceGood, OriginalUpper.upper pool payload' targetGood⟩
      case arrow.arrow input incoming output outgoing input' incoming' output' outgoing' =>
        exact ⟨Or.inl ⟨targetGood.1.lower pool input', sourceGood.1.upper pool input⟩,
          Or.inl ⟨sourceGood.2.lower pool output, targetGood.2.upper pool output'⟩⟩

theorem dispatchOriginal_weak (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (sourceLower : LowerRef pool sourceRef) (sourceGood : SourceGrammar pool source)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (targetGrammar : PresenceGeneratedChildGrammar.upper target = true) (targetGood : UpperRef pool targetRef) :
    OutputWeak pool (dispatchOriginal pool sourceRef source target member targetRef) := by
  cases target with
  | var => simpa [dispatchOriginal, OutputWeak] using weak_edge pool sourceRef targetRef sourceLower targetGood
  | emptyRecord => exact width_weak pool source sourceGood
  | required label payload =>
      apply required_weak pool source sourceGood
      exact ⟨CommonOptionalPoolQueries.required_query pool label payload member,
        by simpa only [PayloadUpper, Pool.child, Pool.termAt_reference,
          PresenceGeneratedChildGrammar.upper] using targetGrammar⟩
  | base scalar => exact rigid_weak pool source sourceGood (.base scalar) trivial targetRef targetGood
  | pair first last =>
      apply rigid_weak pool source sourceGood _ _ targetRef targetGood
      simpa only [RigidGrammar, OriginalUpper, Pool.child, Pool.termAt_reference,
        PresenceGeneratedChildGrammar.upper, Bool.and_eq_true]
        using targetGrammar
  | arrow input incoming output outgoing =>
      apply rigid_weak pool source sourceGood _ _ targetRef targetGood
      simpa only [RigidGrammar, OriginalUpper, Pool.child, Pool.termAt_reference,
        PresenceGeneratedChildGrammar.upper, Bool.and_eq_true]
        using targetGrammar
  | _ => cases targetGrammar

theorem dispatch_weak (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (sourceLower : LowerRef pool sourceRef) (sourceGood : SourceGrammar pool source)
    (target : Ref pool) (targetGood : UpperRef pool target) :
    OutputWeak pool (dispatch pool sourceRef source target) := by
  cases target with
  | original index =>
      exact dispatchOriginal_weak pool sourceRef source sourceLower sourceGood
        _ _ (.original index) targetGood targetGood
  | top => simp [dispatch, OutputWeak]
  | width => exact width_weak pool source sourceGood
  | required label payload => exact required_weak pool source sourceGood label payload targetGood
  | optional label payload => exact optional_weak pool source sourceGood label payload targetGood
  | exactEmpty => cases targetGood

/-- Every returned child edge has the same lower/upper provenance as the
input. Auxiliary required/optional references never become source nodes. -/
theorem inspect_polarity (pool : Pool m) (source target : Ref pool)
    (first : LowerRef pool source) (last : UpperRef pool target) :
    OutputPolar pool (inspect pool source target) := by
  obtain ⟨layer, found⟩ := sourceLayer_some pool source first
  have weak := dispatch_weak pool source layer first (sourceLayer_grammar pool source first layer found) target last
  simpa only [inspect, rawInspect, found] using prune_polar pool _ weak

theorem inspected_child_polarity (pool : Pool m) (source target : Ref pool)
    (first : LowerRef pool source) (last : UpperRef pool target)
    (branch : List (InputCheck pool)) (returned : branch ∈ inspect pool source target)
    (childSource childTarget : Ref pool) (included : edge childSource childTarget ∈ branch) :
    LowerRef pool childSource ∧ UpperRef pool childTarget :=
  inspect_polarity pool source target first last branch returned _ included

end Yulang.CommonBoundRefInspection
