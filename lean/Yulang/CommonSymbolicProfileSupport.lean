import Yulang.CommonSymbolicSourceProfiles

/-!
# Finite support and coherence of symbolic record profiles

The support is a list of syntax references, computed before interpretation.
It distinguishes Boolean guards, optional/field projection queries, and
ordinary guarded payload references. Every query keeps its original node,
label and accumulated outer mask.

Finite support is not an independence claim. A field projection, an optional
projection and presence at the same node must come from one common type.
`CommonSymbolicProfileCoherence` states that separate reconstruction condition.
No worklist closure, saturation termination or unconstrained parameter-family
theorem is asserted here.
-/

namespace Yulang.CommonSymbolicProfileSupport

open Common (Ty Row)
open CommonPayloadProjection (Payload)
open CommonSymbolicRecordProfiles
open CommonSymbolicSourceProfiles (ofNode compileNode compileSlot)
open PresenceOpenTailGenerationLowering (Pool subterms)
open Core.PresenceGeneration (TyTerm)

universe u v w

structure Query (Node : Type u) where
  kind : ProjectionKind
  hidden : List Nat
  label : Nat
  node : Node

inductive Reference (Node : Type u) (Child : Type v) where
  | guard : GuardAtom Node → Reference Node Child
  | projection : Query Node → Reference Node Child
  | payload : Child → Reference Node Child

def payloadReferences : Payload Child → List (Reference Node Child)
  | .ref child => [.payload child]
  | .bottom | .top => []
  | .union first last | .inter first last => payloadReferences first ++ payloadReferences last

def boolReferences : BoolExpr Node → List (Reference Node Child)
  | .literal _ => []
  | .atom query => [.guard query]
  | .and first last | .or first last => boolReferences first ++ boolReferences last
  | .not source => boolReferences source

def profileReferences : ProfileExpr Node Child → List (Reference Node Child)
  | .none => []
  | .some payload => payloadReferences payload
  | .project kind hidden label node => [.projection ⟨kind, hidden, label, node⟩]
  | .both first last | .either first last => profileReferences first ++ profileReferences last
  | .withTrivial source => profileReferences source
  | .ite condition yes no => boolReferences condition ++ profileReferences yes ++ profileReferences no

def summaryReferences (summary : Summary Node Child) : List (Reference Node Child) :=
  boolReferences summary.records ++ boolReferences summary.outsideRecords ++
    boolReferences summary.present ++ boolReferences summary.initialField ++
    boolReferences summary.initialOptional ++ profileReferences summary.field ++ profileReferences summary.optional

/-- These seven modes are the whole primitive interface of one queried
same-depth node. Payloads are separate and never acquire a query mask. -/
def queryReferences (hidden : List Nat) (label : Nat) (node : Node) : List (Reference Node Child) :=
  [.guard (.records node), .guard (.outsideRecords node), .guard (.present hidden label node),
    .guard (.initialField hidden label node), .guard (.initialOptional hidden label node),
    .projection ⟨.field, hidden, label, node⟩, .projection ⟨.optional, hidden, label, node⟩]

/-- Mask accumulation follows only same-depth syntax. Guarded payloads are
not traversed and cannot introduce a fresh outer query location. -/
def nodeLocations (hidden : List Nat) : OpenLayer Rows Node Child → List (List Nat × Node)
  | .ref node => [(hidden, node)]
  | .union first last | .inter first last => nodeLocations hidden first ++ nodeLocations hidden last
  | .record _ _ tail | .recordDefault _ tail _ => nodeLocations hidden tail
  | .mask more source => nodeLocations (hidden ++ more) source
  | _ => []

def guardedChildren : OpenLayer Rows Node Child → List Child
  | .union first last | .inter first last => guardedChildren first ++ guardedChildren last
  | .pair first last | .arrow first _ last _ => [first, last]
  | .record _ payload tail => payload :: guardedChildren tail
  | .recordDefault _ source fallback => fallback :: guardedChildren source
  | .variant _ payload => [payload]
  | .mask _ source => guardedChildren source
  | _ => []

def referenceUniverse (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child) :
    List (Reference Node Child) :=
  (nodeLocations hidden source).flatMap (fun location => queryReferences location.1 label location.2) ++
    (guardedChildren source).map Reference.payload

def Fits (allowed : Reference Node Child → Prop) (references : List (Reference Node Child)) : Prop :=
  ∀ reference ∈ references, allowed reference

private theorem union_fits (allowed : Reference Node Child → Prop) (first last : Summary Node Child)
    (before : Fits allowed (summaryReferences first)) (after : Fits allowed (summaryReferences last)) :
    Fits allowed (summaryReferences (Summary.union first last)) := by
  intro reference member
  have left := before reference
  have right := after reference
  simp only [summaryReferences, Summary.union, boolReferences, profileReferences, List.mem_append] at member left right
  grind

private theorem inter_fits (allowed : Reference Node Child → Prop) (first last : Summary Node Child)
    (before : Fits allowed (summaryReferences first)) (after : Fits allowed (summaryReferences last)) :
    Fits allowed (summaryReferences (Summary.inter first last)) := by
  intro reference member
  have left := before reference
  have right := after reference
  simp only [summaryReferences, Summary.inter, boolReferences, profileReferences, List.mem_append] at member left right
  grind

private theorem record_fits (allowed : Reference Node Child → Prop) (hidden : List Nat)
    (label current : Nat) (payload : Child) (tail : Summary Node Child)
    (child : allowed (.payload payload)) (remaining : Fits allowed (summaryReferences tail)) :
    Fits allowed (summaryReferences (Summary.record hidden label current payload tail)) := by
  intro reference member
  have rest := remaining reference
  by_cases active : label = current ∧ current ∉ hidden
  · simp only [Summary.record, ite_eq_left active, summaryReferences, boolReferences,
      profileReferences, payloadReferences, List.mem_append, List.mem_cons, List.not_mem_nil, false_or, or_false] at member
    rcases member with same | same <;> simpa only [same] using child
  · simp only [Summary.record, ite_eq_right active, summaryReferences, boolReferences,
      profileReferences, List.mem_append, List.not_mem_nil, false_or] at member
    simp only [summaryReferences, List.mem_append] at rest
    grind

private theorem default_fits (allowed : Reference Node Child → Prop) (hidden : List Nat)
    (label current : Nat) (source : Summary Node Child) (fallback : Child)
    (remaining : Fits allowed (summaryReferences source)) (child : allowed (.payload fallback)) :
    Fits allowed (summaryReferences (Summary.recordDefault hidden label current source fallback)) := by
  intro reference member
  have rest := remaining reference
  by_cases active : label = current ∧ current ∉ hidden
  · simp only [Summary.recordDefault, ite_eq_left active, summaryReferences, boolReferences,
      profileReferences, payloadReferences, List.mem_append, List.mem_cons, List.not_mem_nil, false_or, or_false] at member
    simp only [summaryReferences, List.mem_append] at rest
    grind
  · simp only [Summary.recordDefault, ite_eq_right active, summaryReferences, boolReferences,
      profileReferences, List.mem_append, List.not_mem_nil, false_or] at member
    simp only [summaryReferences, List.mem_append] at rest
    grind

/-- A structural support theorem with arbitrary allowed references. It can
be reused with a finite universe or with a semantic coherence predicate. -/
theorem compile_fits (allowed : Reference Node Child → Prop) (hidden : List Nat)
    (label : Nat) (source : OpenLayer Rows Node Child)
    (locations : ∀ location ∈ nodeLocations hidden source,
      Fits allowed (queryReferences location.1 label location.2))
    (children : ∀ child ∈ guardedChildren source, allowed (.payload child)) :
    Fits allowed (summaryReferences (compile hidden label source)) := by
  induction source generalizing hidden with
  | ref node =>
      simpa [compile, Summary.ref, summaryReferences, boolReferences, profileReferences, queryReferences] using
        locations (hidden, node) (by simp [nodeLocations])
  | bottom | top | base | pair | emptyRecord | variant | arrow =>
      simp [compile, Summary.bottom, Summary.top, Summary.scalar, Summary.emptyRecord,
        summaryReferences, boolReferences, profileReferences, payloadReferences, Fits]
  | exactEmpty =>
      by_cases member : label ∈ hidden <;>
        simp [compile, Summary.exactEmpty, member, summaryReferences, boolReferences,
          profileReferences, payloadReferences, Fits]
  | union first last before after | inter first last before after =>
      have left := before hidden
        (fun location member => locations location (List.mem_append_left _ member))
        (fun child member => children child (List.mem_append_left _ member))
      have right := after hidden
        (fun location member => locations location (List.mem_append_right _ member))
        (fun child member => children child (List.mem_append_right _ member))
      first | exact union_fits allowed _ _ left right | exact inter_fits allowed _ _ left right
  | record current payload tail ih =>
      exact record_fits allowed hidden label current payload _
        (children payload (by simp [guardedChildren]))
        (ih hidden locations (fun child member => children child (List.mem_cons_of_mem _ member)))
  | recordDefault current source fallback ih =>
      exact default_fits allowed hidden label current _ fallback
        (ih hidden locations (fun child member => children child (List.mem_cons_of_mem _ member)))
        (children fallback (by simp [guardedChildren]))
  | mask more source ih => exact ih (hidden ++ more) locations children

theorem compile_support (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child) :
    Fits (fun reference => reference ∈ referenceUniverse hidden label source)
      (summaryReferences (compile hidden label source)) := by
  apply compile_fits
  · intro location member reference present
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨location, member, present⟩)
  · intro child member
    exact List.mem_append_right _ (List.mem_map.mpr ⟨child, member, rfl⟩)

theorem projection_queryReferences (query : Query Node) (hidden : List Nat) (label : Nat) (node : Node) :
    Reference.projection query ∈ (queryReferences hidden label node : List (Reference Node Child)) ↔
      query.hidden = hidden ∧ query.label = label ∧ query.node = node := by
  cases query with
  | mk kind queryHidden queryLabel queryNode =>
      cases kind <;> simp [queryReferences, Query.mk.injEq]

theorem projection_in_universe (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child)
    (query : Query Node) :
    Reference.projection query ∈ referenceUniverse hidden label source ↔
      query.label = label ∧ (query.hidden, query.node) ∈ nodeLocations hidden source := by
  simp only [referenceUniverse, List.mem_append, List.mem_flatMap, List.mem_map]
  constructor
  · rintro (⟨⟨mask, node⟩, member, projected⟩ | ⟨child, _, impossible⟩)
    · obtain ⟨sameMask, sameLabel, sameNode⟩ := (projection_queryReferences query mask label node).mp projected
      exact ⟨sameLabel, by simpa only [sameMask, sameNode] using member⟩
    · cases impossible
  · rintro ⟨sameLabel, member⟩
    exact Or.inl ⟨(query.hidden, query.node), member,
      (projection_queryReferences query query.hidden label query.node).mpr ⟨rfl, sameLabel, rfl⟩⟩

theorem payload_in_universe (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child)
    (child : Child) :
    Reference.payload child ∈ referenceUniverse hidden label source ↔ child ∈ guardedChildren source := by
  simp [referenceUniverse, List.mem_flatMap, queryReferences]

def guardNode : GuardAtom Node → Node
  | .records node | .outsideRecords node | .present _ _ node | .initialField _ _ node
  | .initialOptional _ _ node => node

def guardQuery : GuardAtom Node → Option (List Nat × Nat)
  | .records _ | .outsideRecords _ => none
  | .present hidden label _ | .initialField hidden label _ | .initialOptional hidden label _ =>
      some (hidden, label)

theorem guard_queryReferences (query : GuardAtom Node) (hidden : List Nat) (label : Nat) (node : Node)
    (member : Reference.guard query ∈ (queryReferences hidden label node : List (Reference Node Child))) :
    guardNode query = node ∧
      ∀ mask current, guardQuery query = some (mask, current) → mask = hidden ∧ current = label := by
  cases query <;> simp_all [queryReferences, guardNode, guardQuery]

theorem guard_in_universe (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child)
    (query : GuardAtom Node) (member : Reference.guard query ∈ referenceUniverse hidden label source) :
    ∃ mask, (mask, guardNode query) ∈ nodeLocations hidden source ∧
      ∀ currentHidden currentLabel, guardQuery query = some (currentHidden, currentLabel) →
        currentHidden = mask ∧ currentLabel = label := by
  rcases List.mem_append.mp member with member | impossible
  · obtain ⟨⟨mask, node⟩, location, primitive⟩ := List.mem_flatMap.mp member
    obtain ⟨sameNode, sameQuery⟩ := guard_queryReferences query mask label node primitive
    exact ⟨mask, by simpa only [sameNode] using location, sameQuery⟩
  · obtain ⟨child, _, impossible⟩ := List.mem_map.mp impossible
    cases impossible

/-- The complete mask path is syntactic. No labels from a chosen type value
or from a guarded payload enter the outer mask. -/
theorem nodeLocations_prefix (hidden : List Nat) (source : OpenLayer Rows Node Child) :
    nodeLocations hidden source =
      (nodeLocations [] source).map (fun location => (hidden ++ location.1, location.2)) := by
  induction source generalizing hidden with
  | ref node => simp [nodeLocations]
  | union first last before after | inter first last before after =>
      simp only [nodeLocations, List.map_append]
      rw [before hidden, after hidden]
  | record _ _ tail ih | recordDefault _ tail _ ih => exact ih hidden
  | mask more source ih =>
      change nodeLocations (hidden ++ more) source =
        (nodeLocations more source).map (fun location => (hidden ++ location.1, location.2))
      rw [ih (hidden ++ more), ih more]
      simp only [List.map_map, Function.comp_def, List.append_assoc]
  | _ => rfl

theorem compiled_projection_identity (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child)
    (query : Query Node) (member : Reference.projection query ∈ summaryReferences (compile hidden label source)) :
    query.label = label ∧
      ∃ suffix, (suffix, query.node) ∈ nodeLocations [] source ∧ query.hidden = hidden ++ suffix := by
  obtain ⟨sameLabel, location⟩ := (projection_in_universe hidden label source query).mp
    (compile_support hidden label source _ member)
  rw [nodeLocations_prefix] at location
  obtain ⟨⟨suffix, node⟩, original, same⟩ := List.mem_map.mp location
  have sameMask : hidden ++ suffix = query.hidden := congrArg Prod.fst same
  have sameNode : node = query.node := congrArg Prod.snd same
  exact ⟨sameLabel, suffix, by simpa only [sameNode] using original, sameMask.symm⟩

theorem compiled_payload_identity (hidden : List Nat) (label : Nat) (source : OpenLayer Rows Node Child)
    (child : Child) (member : Reference.payload child ∈ summaryReferences (compile hidden label source)) :
    child ∈ guardedChildren source :=
  (payload_in_universe hidden label source child).mp (compile_support hidden label source _ member)

variable {m : Nat}

def sameDepthNodes (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : List (Fin pool.size) :=
  (nodeLocations [] (ofNode pool term member)).map Prod.snd

theorem ofNode_locations (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (hidden : List Nat) :
    nodeLocations hidden (ofNode pool term member) =
      (sameDepthNodes pool term member).map (fun node => (hidden, node)) := by
  cases term <;> rfl

/-- Actual source terms contain no mask constructor. A query therefore keeps
the supplied outer mask literally, not merely up to set equality. -/
theorem compileNode_projection_identity (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (hidden : List Nat) (label : Nat) (query : Query (Fin pool.size))
    (used : Reference.projection query ∈ summaryReferences (compileNode pool hidden label term member)) :
    query.hidden = hidden ∧ query.label = label ∧ query.node ∈ sameDepthNodes pool term member := by
  obtain ⟨sameLabel, location⟩ := (projection_in_universe hidden label (ofNode pool term member) query).mp
    (compile_support hidden label (ofNode pool term member) _ used)
  rw [ofNode_locations] at location
  obtain ⟨node, original, same⟩ := List.mem_map.mp location
  have sameHidden : hidden = query.hidden := congrArg Prod.fst same
  have sameNode : node = query.node := congrArg Prod.snd same
  exact ⟨sameHidden.symm, sameLabel, by simpa only [sameNode] using original⟩

theorem compileNode_guard_identity (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (hidden : List Nat) (label : Nat) (query : GuardAtom (Fin pool.size))
    (used : Reference.guard query ∈ summaryReferences (compileNode pool hidden label term member)) :
    guardNode query ∈ sameDepthNodes pool term member ∧
      ∀ mask current, guardQuery query = some (mask, current) → mask = hidden ∧ current = label := by
  obtain ⟨mask, location, identity⟩ := guard_in_universe hidden label (ofNode pool term member) query
    (compile_support hidden label (ofNode pool term member) _ used)
  rw [ofNode_locations] at location
  obtain ⟨node, original, same⟩ := List.mem_map.mp location
  have sameHidden : hidden = mask := congrArg Prod.fst same
  have sameNode : node = guardNode query := congrArg Prod.snd same
  exact ⟨by simpa only [sameNode] using original, fun current label sameQuery =>
    ⟨(identity current label sameQuery).1.trans sameHidden.symm, (identity current label sameQuery).2⟩⟩

theorem guarded_child_is_subterm (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (child : Fin pool.size) (used : child ∈ guardedChildren (ofNode pool term member)) :
    pool.termAt child ∈ subterms term := by
  cases term <;>
    simp_all [ofNode, guardedChildren, Pool.child, Pool.termAt_reference, subterms]
  all_goals rcases used with rfl | rfl <;> simp

theorem compileNode_payload_identity (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (hidden : List Nat) (label : Nat) (child : Fin pool.size)
    (used : Reference.payload child ∈ summaryReferences (compileNode pool hidden label term member)) :
    child ∈ guardedChildren (ofNode pool term member) ∧ pool.termAt child ∈ subterms term := by
  have guarded := compiled_payload_identity hidden label (ofNode pool term member) child used
  exact ⟨guarded, guarded_child_is_subterm pool term member child guarded⟩

/-- A fixed query needs at most these eight reference kinds per original
node. This bound concerns syntax support, not all future saturation states. -/
def poolUniverse (pool : Pool m) (hidden : List Nat) (label : Nat) :
    List (Reference (Fin pool.size) (Fin pool.size)) :=
  (List.ofFn fun node : Fin pool.size => node).flatMap fun node =>
    queryReferences hidden label node ++ [.payload node]

theorem query_mem_poolUniverse (pool : Pool m) (hidden : List Nat) (label : Nat) (node : Fin pool.size)
    (reference : Reference (Fin pool.size) (Fin pool.size)) (member : reference ∈ queryReferences hidden label node) :
    reference ∈ poolUniverse pool hidden label :=
  List.mem_flatMap.mpr ⟨node, List.mem_ofFn.mpr ⟨node, rfl⟩, List.mem_append_left _ member⟩

theorem payload_mem_poolUniverse (pool : Pool m) (hidden : List Nat) (label : Nat) (node : Fin pool.size) :
    Reference.payload node ∈ poolUniverse pool hidden label :=
  List.mem_flatMap.mpr ⟨node, List.mem_ofFn.mpr ⟨node, rfl⟩,
    List.mem_append_right _ List.mem_cons_self⟩

theorem compileNode_pool_support (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (hidden : List Nat) (label : Nat) :
    Fits (fun reference => reference ∈ poolUniverse pool hidden label)
      (summaryReferences (compileNode pool hidden label term member)) := by
  apply compile_fits
  · intro location atLocation reference primitive
    rw [ofNode_locations] at atLocation
    obtain ⟨node, _, rfl⟩ := List.mem_map.mp atLocation
    exact query_mem_poolUniverse pool hidden label node reference primitive
  · intro child _
    exact payload_mem_poolUniverse pool hidden label child

theorem poolUniverse_length (pool : Pool m) (hidden : List Nat) (label : Nat) :
    (poolUniverse pool hidden label).length = 8 * pool.size := by
  have length (nodes : List (Fin pool.size)) :
      (nodes.flatMap (fun node => (queryReferences hidden label node :
        List (Reference (Fin pool.size) (Fin pool.size))) ++ [.payload node])).length = 8 * nodes.length := by
    induction nodes with
    | nil => rfl
    | cons node rest ih =>
        rw [List.flatMap_cons, List.length_append]
        change 8 + (rest.flatMap (fun node => (queryReferences hidden label node :
          List (Reference (Fin pool.size) (Fin pool.size))) ++ [.payload node])).length = 8 * (rest.length + 1)
        rw [ih, Nat.mul_add]
        omega
  simpa only [poolUniverse, List.length_ofFn] using length (List.ofFn fun node : Fin pool.size => node)

def queriesUniverse (pool : Pool m) (queries : List (List Nat × Nat)) :
    List (Reference (Fin pool.size) (Fin pool.size)) :=
  queries.flatMap (fun query => poolUniverse pool query.1 query.2)

theorem compileNode_queries_support (pool : Pool m) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (queries : List (List Nat × Nat)) (hidden : List Nat) (label : Nat) (queryPresent : (hidden, label) ∈ queries) :
    Fits (fun reference => reference ∈ queriesUniverse pool queries)
      (summaryReferences (compileNode pool hidden label term member)) := by
  intro reference used
  exact List.mem_flatMap.mpr ⟨(hidden, label), queryPresent,
    compileNode_pool_support pool term member hidden label reference used⟩

theorem queriesUniverse_length (pool : Pool m) (queries : List (List Nat × Nat)) :
    (queriesUniverse pool queries).length = 8 * pool.size * queries.length := by
  induction queries with
  | nil => rfl
  | cons query rest ih =>
      change (poolUniverse pool query.1 query.2 ++ queriesUniverse pool rest).length =
        8 * pool.size * (rest.length + 1)
      rw [List.length_append, poolUniverse_length, ih, Nat.mul_add]
      simp only [Nat.mul_one, Nat.add_comm]

end Yulang.CommonSymbolicProfileSupport
