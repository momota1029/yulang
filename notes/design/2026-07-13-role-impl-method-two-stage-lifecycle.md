# Role impl method two-stage lifecycle design

Date: 2026-07-13

Status: **implemented and verified for the approved two-stage role-impl method lifecycle
(2026-07-14).** The separate candidate-independent early-fallback production optimization was
investigated and deferred.

## 1. Purpose and relationship to the conformance specification

Stage 2 needs an actual method surface that has seen the implementation body and its own source
annotations, but has not been narrowed by the role method requirement it is supposed to satisfy.
Stage 2 Slice 0 established two facts:

1. source `U/A` identities can be bridged to same-session inference variables if the bridge is
   retained in production; and
2. the finalized method scheme is too late, because requirement-derived constraints have already
   entered the production constraint graph.

The initial idea was to snapshot immediately before one requirement connection. Code inspection
showed that there is no such common point for all role impl methods. Receiver methods receive
requirement constraints before, during, and after body lowering. In addition, the analysis work
queue is drained only after all source bodies have been lowered, so an immediate compact snapshot
would omit later selection, reference, SCC, role-resolution, and generalization effects.

This document specifies a bounded pending lifecycle that keeps a source method's SCC component open
until ordinary body analysis is quiescent, captures a read-only pre-requirement view, applies the
legacy requirement connections exactly once, settles their effects, and only then permits ordinary
quantification.

It refines Stage 2 Slice 2 and later actual-side work. It does not change the already implemented
declared-side view from Stage 2 Slice 1.

## 2. Verified current timeline

### 2.1 Candidate and method registration

For each source role impl:

1. `BodyLowerer::register_role_impl_candidate` captures the source conformance contract and inserts
   the raw `RoleImplCandidate` before lowering method bodies.
2. `BodyLowerer::lower_role_impl_method` enters a child inference level, allocates the method root,
   records it in `Typing`, and enqueues `SccInput::RegisterDef`.
3. A non-private method is recorded as an impl member. When a role requirement is found,
   `register_role_impl_member_requirement` enqueues `SccInput::DependencyAdded` from the member to
   the role method definition.
4. The body is lowered synchronously into the shared `ConstraintMachine`.
5. `finish_binding` writes the expression body, connects the method root to the lowered method
   value, records fetch information, and enqueues `SccInput::DefFinished`.

These SCC inputs are queued. They are not necessarily applied while that method is being lowered.

### 2.2 Requirement connections during body lowering

Receiverless and receiver methods follow different paths.

#### Receiverless method

1. `lower_lambda_params` lowers the complete method value without a role-requirement plan.
2. `connect_impl_method_requirement(..., connect_value_upper = true)` runs once afterward.
3. It performs read-only shape/concrete checks, lowers the complete requirement upper, adds
   `method_value <: requirement`, and records the requirement projection and simplification used by
   impl-prerequisite collection.

This path has a local pre-connection anchor, but the analysis queue is still undrained at that
point.

#### Receiver method

1. The receiver is connected to the impl target annotation.
2. `impl_method_requirement_plan` lowers the declared function spine before the body. It creates
   parameter uppers and a body value/effect upper using the shared annotation-to-solver mapping.
3. Each tail parameter is connected to its requirement upper before lowering the body.
4. The body and its nested expressions are lowered. Source result annotations, when present, use
   `AnnConstraintLowerer::connect_computation_detailed` before the role requirement body edge.
5. `connect_impl_method_body_requirement` adds exactly two role-derived subtype edges:
   `body.effect <: required effect` and `body.value <: required value`.
6. The receiver and tail lambdas are wrapped into the complete method value.
7. `connect_impl_method_requirement(..., connect_value_upper = false)` performs final checks and
   records projection/simplification metadata. It does not add a whole-value upper on this path.

The call to `connect_impl_method_body_requirement` occurs at most once per receiver method, through
one of two exclusive lambda-tail branches. It is nevertheless not a clean pre-requirement point:
parameter requirements and signature-lowering facts have already entered the machine.

`AnnConstraintLowerer::connect_computation_detailed` is not the role-requirement connector. Its
production uses here are source result annotations, expression-tail annotations, and local binding
annotations. Those belong to the implementation's actual surface and must not be removed.

### 2.3 Work drain and quantification

`lower_binding_bodies` and the loaded-file variants lower every body first. They then call
`AnalysisSession::drain_work`.

For each queued item, the session:

1. routes pending constraint events;
2. applies reference, selection, or SCC work;
3. routes SCC events; and
4. repeats until the queue and unresolved-role pass stop making progress.

The SCC machine owns quantification readiness. An open component is removed and emits
`SccEvent::QuantifyComponent` only when:

- every member has a registered root;
- every member has received `DefFinished`;
- the component has no outgoing SCC edge; and
- its unresolved method-dependency count is zero.

Routing `QuantifyComponent` immediately calls `AnalysisSession::quantify_component`. Each root is
generalized with the existing merge/subtype/cast/role prepasses, impl-member prerequisites are
collected, schemes are finalized into the poly arena, and the component remains in the SCC
machine's quantified set. Later uses instantiate those schemes; the component is not reopenable.

Therefore a requirement edge cannot safely be applied after committed quantification. Doing so
would mutate inference variables whose published scheme was derived from an earlier graph, while
the SCC machine would still consider the definition final.

## 3. Required invariants

A two-stage implementation must preserve all of the following:

1. Every pending method is processed at most once before ordinary quantification.
2. Every method in one ready SCC component is snapshotted before any pending edge in that component
   is applied.
3. Existing source annotations remain part of the actual surface.
4. Requirement parameter context that is intentionally needed to typecheck a body is distinguished
   from the result/effect claim being validated.
5. The legacy requirement edges and projection/simplification metadata are still applied before
   the production scheme is quantified during shadow stages.
6. Constraint events caused by the delayed edges settle before the conformance blocker is released.
7. A failed or unsupported snapshot records a structured failure but still releases the SCC after
   restoring legacy connections, so analysis cannot deadlock.
8. Imported/cache methods and ordinary functions do not enter this source-only lifecycle.
9. No raw `TypeVar` becomes canonical identity. The production bridge is same-session transport
   metadata only.

## 4. Literal "generalize then connect" is not safe

A literal sequence of:

```text
generalize and publish scheme
apply pending requirement edge
continue compilation
```

is invalid under the current SCC contract. Once `QuantifyComponent` runs, the component is removed
from the open graph and incoming uses are converted to scheme instantiations. There is no supported
operation to invalidate the scheme, reopen the component, retract instantiations, or replay
downstream constraints.

Running one complete generalization for the actual view and a second complete generalization after
applying the pending edge would avoid a stale scheme but violates Section 16's explicit ban on a
second generalization loop. It also risks order-dependent results when several roots in one SCC
share variables.

The implementable interpretation is therefore:

```text
ordinary body analysis reaches SCC-ready quiescence
build one immutable, generalization-equivalent actual view without publishing a scheme
apply each pending requirement connection once
settle resulting work while the component remains open
release the component
run the existing ordinary quantification exactly once
```

"Generalization-equivalent" is deliberately constrained. It may reuse read-only compact and
finalization traversals, but it may not run the production mutation/restart loop a second time. If
the view requires an unapplied merge, subtype, cast, or role-resolution fact, that case is
`Unavailable` in the early implementation and fails closed in later enforcement. It must not be
made to pass by adding a shadow solver loop.

## 5. Proposed pending state

### 5.1 Session-owned records

Illustrative internal data structures:

```rust
struct PendingRoleImplMethodTable {
    by_member: FxHashMap<DefId, PendingRoleImplMethod>,
    actual_views: FxHashMap<DefId, ActualMethodConformanceView>,
    failures: Vec<RoleImplConformanceCaptureFailure>,
}

struct PendingRoleImplMethod {
    impl_def: DefId,
    member: DefId,
    role_method: DefId,
    anchors: PendingMethodActualAnchors,
    requirement: ResolvedRoleMethodRequirement,
    deferred_requirement: DeferredRoleRequirementConnection,
    phase: PendingMethodPhase,
}

enum PendingMethodActualAnchors {
    Receiverless {
        method_value: TypeVar,
    },
    Receiver {
        receiver: TypeVar,
        parameters: Vec<TypeVar>,
        body_value: TypeVar,
        body_effect: TypeVar,
        method_value: TypeVar,
    },
}

enum PendingMethodPhase {
    Captured,
    SnapshotTakenEdgesApplied,
    Released,
    FailedAndEdgesApplied,
}
```

`DeferredRoleRequirementConnection` is intentionally not specified as only a name-to-`TypeVar`
seed. One `SignatureLowerer` currently shares method-local signature variables, closed effect-row
variables, and private data-effect tails while lowering parameter and body layers. Re-lowering the
body later from only the original seed could allocate different method-local identities and would
not faithfully reproduce the legacy connection.

Slice 0 must distinguish two cases:

1. lowering the complete requirement spine without attaching its body upper does not change any
   actual bridge variable; in that case the pending record may safely retain the already-lowered
   body connection and parameter uppers; or
2. expected-signature lowering itself changes the actual surface; in that case `SignatureLowerer`
   needs an explicit same-session continuation state containing all relevant variable/row/private-
   tail maps, or the parameter context must also be deferred.

Inventing that continuation from `SignatureType` plus a fresh seed is not acceptable. Its identity
requirements must be characterized before selecting the representation.

The exact fields remain subject to Stage 2 actual-view needs. The important properties are:

- the record is keyed by source member `DefId`;
- expected signature data is retained structurally, not recovered by CST rescanning;
- the exact legacy signature-lowering identity is retained separately from the logical `U/A`
  bridge;
- pending expected uppers are not lowered before the actual snapshot if lowering them would mutate
  shared `U/A` inference variables; and
- every phase transition is monotonic and bounded.

`RoleImplConformanceContract` should formally retain a separate bridge:

```rust
struct RoleImplConformanceBinderBridge {
    universals: Vec<(ImplUniversalBinderId, TypeVar)>,
    inferred_associated: Vec<(AssociatedInferenceBinderId, TypeVar)>,
}
```

The bridge is produced once after `ann_solver_vars` is complete. Missing mappings become a
structured `Unavailable` result; they are not reconstructed from final raw IDs. If a known
annotation-identity overlap maps `U` and `A` to the same solver variable, both logical entries are
retained.

#### 5.1.1 Slice 1 revision after lifecycle characterization

Slice 0 resolved the earlier two-case question in the harder direction. Lowering only temporary
expected nodes is already a mutating operation for effect-bearing `U/A`: return-effect tails gain
declared subtract facts, and an effect-row parameter can gain both lower and upper bounds, before
the temporary upper is attached to an actual parameter or body anchor. The plain value-position
case remains non-mutating, but it is not a valid model for the language-wide design.

This separates two properties which the earlier continuation sketch left implicit:

1. retaining `SignatureLowerer` state can preserve same-session identities across a pause; but
2. retaining state after the complete spine has already been lowered cannot make the earlier
   mutation disappear from the actual surface.

Therefore the literal continuation-state option -- lower the complete requirement spine at the
current point, capture the lowerer afterward, and merely delay attachment of its uppers -- is not a
sound pre-requirement snapshot boundary. A viable continuation design must pause *before* lowering
the deferred body result/effect layer. Early parameter lowering may remain only as explicitly
classified contextual input; effect-bearing parameter context is fail-closed until section 13
point 2 is resolved.

##### Continuation-state feasibility

`SignatureLowerer<'a>` cannot itself be stored in the pending table because it borrows both the
session `Arena` and `ModuleTable`. It must be split into a borrow-free owned state and a short-lived
driver, conceptually:

```rust
struct SignatureLoweringContinuation {
    vars: FxHashMap<String, TypeVar>,
    new_var_level: Option<TypeLevel>,
    closed_effect_rows: FxHashMap<SignatureClosedEffectRowKey, TypeVar>,
    data_effect_private_tails: FxHashMap<DataEffectTailKey, DataEffectPrivateTail>,
}

struct SignatureLowerer<'a> {
    infer: &'a mut Arena,
    modules: &'a ModuleTable,
    state: SignatureLoweringContinuation,
}
```

Existing constructors become state constructors. New `from_continuation` and
`into_continuation` operations borrow the current session only while lowering one uninterrupted
layer. The captured `new_var_level` is mandatory: resuming at the session's later current level
would change extrusion and simplification behavior even if every variable map were preserved.

The structural requirement must also retain stable row-occurrence identity. The current
`DataEffectTailKey` includes the address of a `SignatureEffectRow`; cloning or rebuilding the
`SignatureType` would invalidate that identity. The pending descriptor should therefore own one
immutable same-session allocation, for example `Arc<ResolvedRoleMethodRequirement>`, before the
first layer is lowered. It must never clone the contained `SignatureType`. A borrow-free spine
cursor records the number/path of consumed function layers and re-borrows the same allocation on
resume. This keeps the current address-key behavior bounded to the lifetime of one immutable
requirement. Replacing the address key with an explicit stable row-occurrence ID remains a possible
later cleanup, but its serialization and compiled-signature impact is not yet known and is not part
of Slice 1 by assumption.

The pending receiver descriptor becomes equivalent to:

```rust
struct DeferredReceiverRequirement {
    requirement: Arc<ResolvedRoleMethodRequirement>,
    parameter_uppers: Vec<Option<NegId>>,
    body_cursor: RequirementSpineCursor,
    continuation: SignatureLoweringContinuation,
    parameter_context: RequirementParameterContextStatus,
    final_metadata: DeferredRequirementMetadata,
}

enum RequirementParameterContextStatus {
    Clean(NonMutatingRequirementClass),
    MutatedBridge(BridgeMutationAudit),
    Unsupported(RequirementParameterContextUnavailable),
}

struct BridgeMutationAudit {
    epoch_before: ConstraintEpoch,
    epoch_after: ConstraintEpoch,
    affected: Vec<ConformanceBinderMutation>,
    unexplained_epoch_advance: bool,
}
```

The continuation is captured after only the approved parameter layers have been prepared and
before `lower_impl_requirement_body_connection` runs. At the first quiescent pending phase, the
actual view is taken first; then the same continuation lowers the body result/effect upper exactly
once and the legacy two body edges are applied. The current final projection/simplification call
uses a separate fresh `SignatureLowerer` seed today. To preserve legacy behavior, Slice 1 retains
that final metadata operation structurally and defers it until after the snapshot; it does not
silently merge its identities with the parameter/body continuation.

This route needs a lowering-internal `SignatureLowerer` representation change but no
`ConstraintMachine` API or propagation-semantics change. It adds no retry loop: one continuation is
created once, consumed once, and never reconstructed from `SignatureType` plus a fresh seed.

##### Tagged-mutation feasibility

The current read APIs can characterize an immediate call but cannot support sound fact-level
exclusion:

- `epoch()` says that some state changed but not which fact caused the change;
- `bounds().of(var)` and `subtracts().facts(var)` permit before/after comparison for a known bridge
  variable;
- `events()` can expose the synchronous lower/upper/subtract events emitted during the initial
  lowering call; and
- `next_type_var()` permits a bounded scan of allocated variable IDs if a test or audit needs one.

This is enough for a classification audit: if a known `U/A` bridge changes, or the epoch advances in
a way the bridge snapshots do not explain, the early actual view can return structured
`Unavailable`. It is not enough to remove only requirement-derived facts from a later view. Bounds
carry type nodes and weights but no origin; subtract facts carry an ID and subtractability but no
origin; `lower_filters`, pre-pop effect families, evidence bounds, replayed bounds, and the global
`seen` subtype set also have no complete external provenance view.

It is not even a complete immediate-mutation oracle: insertion into `lower_filters` is not exposed
by the read API and does not itself advance the constraint epoch. Consequently `Clean` cannot mean
"the observed bounds/facts/epoch happened not to change". It is available only for a structurally
defined non-mutating signature subset, initially plain value positions with no effect row,
effectful layer, or act/error effect-family position. The before/after audit is corroborating
evidence and a reason to return `Unavailable`, never the proof that an arbitrary signature is clean.

A complete immediate mutation journal would require a new read-only
`ConstraintMutationSnapshot/Delta` API covering bounds, evidence bounds, subtract facts,
lower filters, pre-pop families, declared-subtract membership, and emitted events. That is roughly
2-4 constraint/lowering files and 150-300 lines including tests. It would improve diagnostics and
auditing, but it still would not carry origin through later body-triggered replay and therefore does
not make selective tagged filtering sound. The adopted Slice 1 does not require this API.

Most importantly, a requirement-derived bound can later meet a body-derived bound. The replay
result is produced after the immediate before/after window and has no tag connecting it back to the
requirement. Adding a sound tag would require origin propagation through `SubtypeConstraint`,
`ConstraintWork`, lower/upper/evidence bounds, subtract facts, row residual work, events, replay,
subsumption, and deduplication. Duplicate constraints would need multi-origin union rather than the
current exact `seen` set, and newly learned origin on an existing constraint might itself require
provenance replay. That is an 8-12 file, roughly 700-1,300 line, very-high-risk solver project, not a
pending-descriptor slice. It approaches the provenance subtraction rejected by section 10.2 and
could accidentally introduce a second propagation fixed point.

A smaller view-side exclusion policy would still require a new compact/view collector input for
excluded weighted bounds and subtract facts, approximately 3-5 files and 250-500 lines. Without
machine provenance it would be unsound for later mixed replay. The only safe use of the current API
is coarse fail-closed classification, not selective subtraction.

##### Slice 1 decision

Slice 1 adopts the owned continuation-state direction, with body result/effect *lowering* deferred,
not merely its final subtype edges. It rejects precise tagged-mutation filtering. A bounded bridge
mutation audit is retained only to classify early parameter preparation as `Clean` or
`Unavailable`. `Clean` requires the conservative structural classifier above; bounds/facts/epoch
equality alone is insufficient. The audit is never consulted by unification,
floor/co-occurrence/polarity simplification, or ordinary compact collection and never removes
solver facts.

This is consistent with section 16: the continuation has one monotonic create/consume lifecycle,
does not add a fixed point, and is not a rigid, blocked, or through mechanism. The tagged approach
would put new policy and provenance into the solver hot path and is therefore the less compatible
direction.

### 5.2 SCC blocker

Reusing `MethodDependencyAdded` as the pending blocker is unsafe. That counter means an unresolved
selection and changes `selection_fallback_ready` behavior. The SCC graph needs a distinct bounded
conformance blocker, conceptually:

```rust
SccInput::ConformancePending { member }
SccInput::ConformanceReleased { member }
```

Each open component tracks the set or count of pending conformance members. Component merge unions
that state. Ordinary `is_ready_to_quantify` additionally requires the count to be zero.

The graph also needs a deterministic read-only query for components that are ready except for
conformance blockers:

```text
all roots registered
all members finished
no outgoing SCC edge
method dependency count is zero
one or more conformance blockers remain
```

The query must not remove the component or emit `QuantifyComponent`.

## 6. Proposed control flow

### 6.1 Lowering phase

For a targeted source method:

1. enqueue/register its conformance blocker before `DefFinished` can settle the component;
2. keep source parameter annotations and approved requirement parameter context;
3. do not lower or connect the requirement body result/effect upper yet;
4. do not create final requirement projection/simplification metadata yet if doing so touches the
   shared bridge variables;
5. capture the actual anchors and the structural requirement in the pending table;
6. finish the binding normally and enqueue `DefFinished`.

The receiver path requires splitting `impl_method_requirement_plan` into:

- contextual parameter preparation, which may run before the body; and
- deferred body/final connection preparation, which retains structural signature data until the
  pending phase.

The receiverless path retains its already-clean whole-method anchor and defers the current final
`connect_impl_method_requirement(..., true)` call.

Read-only shape/concrete checks may remain before capture because they do not mutate constraints.
Any check that relies on facts only available after work drain moves into the pending phase and
must report through a structured post-drain diagnostic path.

### 6.2 First quiescent pending phase

Extend the existing `drain_work` orchestration after normal work and unresolved-role progress stop:

1. ask the SCC machine for the first deterministic component ready except for conformance;
2. collect every `Captured` pending member in that component;
3. build all actual views before applying any pending edge;
4. store successful immutable views or structured failures;
5. lower and apply each member's legacy requirement edges and projection/simplification exactly
   once;
6. transition all records to `SnapshotTakenEdgesApplied` or `FailedAndEdgesApplied`;
7. keep conformance blockers in place and continue the normal drain loop.

No member is released in the same step that applies its edges. This prevents the SCC machine from
emitting `QuantifyComponent` before constraint events, selection probes, newly discovered uses, or
nominal-cast work caused by those edges have settled.

### 6.3 Second quiescent release phase

When the queue becomes quiescent again:

1. find components whose pending members are all in an edges-applied state and which are otherwise
   ready;
2. release all conformance blockers in that component as one deterministic batch;
3. let the existing SCC machine settle the component;
4. route its ordinary `QuantifyComponent` event; and
5. run the existing production generalization exactly once.

If pending edges caused an SCC merge, the blocker state follows the merged component. Newly merged
members must settle before release. Already snapshotted methods are not snapshotted or connected a
second time.

## 7. Blast radius

### 7.1 Initial limited application

The first implementation can and should be limited to methods satisfying all of:

- the method belongs to a source `RoleImplConformanceContract` in the current lowering unit;
- the provision is an explicit source implementation, not a role default;
- every associated assignment for that impl is explicit;
- the declared requirement is available and unambiguous; and
- the method is selected for Stage 2 actual-view shadow capture.

This boundary matches the first enforcement target from the parent specification and avoids making
an ownership decision for omitted/partial associated variables. Methods outside it retain the
current immediate connection path.

The concrete branch point is `BodyLowerer::lower_role_impl_method`, after correspondence and
requirement resolution identify the source member but before `lower_impl_method_body_expr` creates
the requirement plan. It must be driven by structured contract metadata, not a method or role name.

Imported/cache role impls have no source body lowering and remain unchanged. Role default bodies
are role definitions, not explicit impl members, and remain unchanged. Ordinary functions and type
methods remain unchanged.

### 7.2 Unavoidable component-local impact

Even under limited application, every non-target definition in the same SCC component waits while
the pending phase runs. Its constraints and eventual scheme are not changed intentionally, but its
quantification timing is delayed by up to two bounded drain phases.

Pending edges are applied later than today. The constraint system is intended to be order
independent, but that must not be assumed. Shadow tests must compare:

- finalized schemes;
- role candidate prerequisites and method tables;
- selection resolutions;
- SCC merge/quantification events; and
- runtime behavior

against the immediate-connection baseline.

### 7.3 Eventual full application

Whole-role enforcement would eventually cover more source role impl methods. Omitted and partial
associated assignments cannot use only an SCC-local barrier: one inferred `A` may be shared by
methods that are in different SCC components. An impl-wide barrier or a settled associated witness
lifecycle is required before expanding to those cases. That is Stage 6 of the parent specification,
not an assumption of the first implementation.

## 8. SCC and recursion analysis

### 8.1 Mutual recursion inside one component

If a role impl method is mutually recursive with another binding, their resolved use edges merge
them into one open component before readiness. The pending scheduler must snapshot all targeted
members in that component atomically before any pending edge is applied.

The view may contain recursive bounds. Stage 2's `Rm` representation and bounded SCC memoization
must handle those bounds. Until that substep exists, recursive actual views are `Unavailable`; the
legacy edge is still applied and compilation proceeds in shadow mode.

### 8.2 Pending edges that discover more dependencies

A delayed upper may generate constraint events that re-probe a selection. That can add a use edge,
an outgoing dependency, or an SCC merge. Keeping the blocker through a complete subsequent drain is
therefore mandatory.

If a method selection becomes resolvable only after receiving the declared result/effect upper,
the pre-requirement actual view did not independently determine that selection. Enforcement must
not silently use the post-edge resolution to repair the pre-edge proof. It is an unsupported or
context-dependent conformance case until the proof kernel documents such expected-type-directed
resolution.

### 8.3 Separate components sharing impl binders

Universal `U` identities may be shared logically without creating an SCC edge. This is safe for
read-only symbolic comparison when each view replaces the same bridge variable by the same `U`.
Inferred `A` ownership is not equally settled: constraints from multiple methods may jointly infer
one witness without putting the methods in one SCC. The initial explicit-only scope avoids claiming
that SCC readiness is sufficient for `A`.

### 8.4 Failure and deadlock policy

A capture or validation failure cannot leave a blocker installed forever. In shadow mode:

1. record the structured failure;
2. apply the legacy pending edges;
3. settle resulting work;
4. release the blocker; and
5. preserve current compilation success/failure behavior.

In later enforcement mode, the same lifecycle completes but the successful `BodyLowering` result is
rejected by a source diagnostic. The analysis graph still reaches a terminal state.

## 9. Section 16 self-audit

### 9.1 New fixed point

The proposed pending scheduler adds two monotonic transitions per targeted method. It reuses the
existing drain loop, but it must not introduce retry-until-view-success behavior. A method can move
only:

```text
Captured -> EdgesApplied -> Released
```

or through the corresponding failed state. Component merge does not reset a method's phase.

This is a bounded lifecycle state machine, not a new inference fixed point. Nevertheless, adding a
new quiescence phase to `drain_work` is close enough to the forbidden area that tests must assert a
strict upper bound on pending transitions and prove no method is replayed.

### 9.2 Second generalization loop

Calling `generalize_root_with_prepasses` for the snapshot and again for the production scheme is
forbidden. The initial implementation may only use a read-only actual-view traversal. If that
traversal encounters facts that ordinary generalization would need to apply back into the machine,
it returns `Unavailable`.

Alternative if the read-only view proves insufficient: refactor the existing single
generalization pipeline to expose a component-level pre-finalization hook, then obtain explicit
user approval for that larger design. Do not add a second loop as a local workaround.

### 9.3 Recursive unfolding

Actual views use the existing recursive binder graph and bounded memoization. They do not unfold
recursive types until stable. Unsupported recursive shapes fail closed.

### 9.4 Rigid/protected variables and blocked/through flags

The conformance blocker is an SCC lifecycle state, not a type-variable protection mechanism. It
must never be consulted by floor, co-occurrence, polarity simplification, or unification. No rigid
set, blocked pair, through flag, or cache-specific simplification exception is introduced.

There is a naming and design risk: a generic "blocked component" abstraction could drift into a
permanent protection mechanism. Keep the state specific to pending source-method finalization,
monotonic, and absent from all type simplification APIs.

### 9.5 Raw identity and unsupported cases

Raw `TypeVar` values are same-session anchors only. Views translate them through `U/A/Qm/Rm` before
equality or comparison. Missing bridges, unresolved expected-type-directed selections, recursive
views not yet supported, and read-only normalization gaps remain explicit failures. They are not
accepted because later specialize/runtime might reject them.

## 10. Alternatives and rollback points

### 10.1 Isolated shadow replay

Lowering the method a second time without requirement edges avoids SCC lifecycle changes in the
main session, but requires a second module/selection/role environment and risks semantic drift.
Cost and memory are high. It remains the fallback if bounded pending capture cannot produce a sound
actual view without modifying the production generalization loop.

### 10.2 Constraint provenance subtraction

Tagging requirement edges and subtracting their propagated consequences later is not currently
sound. Propagation is not invertible, and the machine has no persistent derivation graph. This
alternative is rejected unless the constraint representation is redesigned independently.

### 10.3 Validation replaces legacy connection

After enforcement is proven complete, a successful immutable conformance proof may make the legacy
result/effect edge redundant. Omitting it would avoid the post-snapshot settle phase. That is a
source-semantic and inference change and is not part of Stage 2 shadow work. It requires separate
acceptance against inferred associated types, predicates, effects, casts, repository std, and cache
routes.

### 10.4 Rollback

Every initial slice must be removable without changing contract capture or the declared view.
Before enforcement, disabling pending mode must restore the exact immediate-connection path. If a
valid std impl changes scheme/candidate/selection behavior under delayed connection, stop and
classify the order dependency rather than updating expected output.

## 11. Acceptance witnesses for the lifecycle

Before actual-view comparison is connected, lifecycle tests must cover:

1. receiverless method: one capture, one edge application, one release;
2. receiver method with zero and multiple tail parameters;
3. source result/effect annotation remains in the pre-requirement view;
4. nested expression/local annotations remain in the view;
5. explicit `value = bool` counterexamples retain `U` in the actual view;
6. alpha-renamed fixtures produce equal actual views;
7. a requirement edge that emits constraint events settles before quantification;
8. two pending methods in one SCC are snapshotted before either edge is applied;
9. a pending method mutually recursive with an ordinary binding delays the complete component;
10. an SCC merge after edge application does not replay any pending method;
11. unsupported recursive/inferred-associated cases record `Unavailable` and terminate;
12. immediate and delayed shadow runs produce identical production schemes, candidates,
    selections, diagnostics, and runtime results for accepted fixtures;
13. transition counters are bounded by two transitions per pending method; and
14. imported/cache/default methods never enter the pending table.

Repository std comparison is mandatory before widening beyond explicit-complete source impls.

## 12. Proposed implementation slices

The complete safe change is size L: approximately 8-12 files and 900-1,600 lines including tests.
Risk is very high because it changes when an open SCC is allowed to quantify and delays constraints
that may drive method selection.

Suggested slices:

### Slice 0: lifecycle characterization

Size S, test-only. Record current event order for receiverless, receiver, recursive, and
multi-member SCC fixtures. Add counters for requirement connections and quantification order. No
behavior change.

Slice 0 completed in the 2026-07-13 session (test-only, no behavior change). Witnesses live in
`crates/infer/src/lowering/tests/case_07.rs`.

- Event order confirmed for receiverless, receiver (zero and two tail parameters),
  mutual-recursion-with-ordinary-binding, and two-role-impl-methods-one-component fixtures:
  `RegisterDef` precedes the observable requirement-dependency component edge, which precedes
  `QuantifyComponent`; merges land before the joint component quantifies. This matches section 2
  exactly.
- Connection counts confirmed: a receiverless method applies exactly one whole-value upper: a
  receiver method applies one edge per tail parameter plus exactly two body edges (value, effect);
  the final `connect_impl_method_requirement` metadata call on the receiver path adds no further
  upper.
- Section 13 point 3 is resolved, in the harder direction. Plain value-position `U`/`A` bridges are
  unmutated by `impl_method_requirement_plan` before its body upper is connected. Effect-typed
  `U`/`A` -- whether a result-effect tail or a full effect-row parameter -- are mutated purely by
  lowering the expected signature: subtract facts and the constraint epoch advance, and for
  effect-row parameters the bounds themselves gain lower/upper entries, before any body or
  parameter upper is actually connected. This confirms section 5.1's "case 2": expected-signature
  lowering itself changes the actual surface for effect-bearing positions.
- `SignatureLowerer`'s internal state sharing (method-local signature variables, closed effect-row
  identity, private data-effect tail) requires the same `SignatureLowerer` instance across the
  parameter and body layers. Re-deriving it later from `SignatureType` plus a fresh seed would not
  reproduce the same identities.

Implication for Slice 1: keeping already-lowered parameter uppers untouched while deferring only the
body result/effect connection does not extend safely to effect-bearing positions, which are common
in this effect-oriented language. Slice 1 must design the explicit same-session continuation state
for `SignatureLowerer` (or defer the expected-signature lowering itself for effect-bearing
positions); it must not assume the plain-value case generalizes. This raises Slice 1's risk and cost
above its original S-M sizing and is a decision point for Claude Sonnet 5 and the user before Slice 1
begins.

### Slice 1: production binder bridge and pending descriptor

Size S-M. Formalize the `U/A -> TypeVar` bridge, split requirement data from already-lowered uppers,
and capture pending anchors behind an inactive/shadow-only path. No SCC behavior change.

Revision after Slice 0: the S-M estimate above is superseded by size M-L, approximately 6-9 files
and 700-1,200 lines including tests, with high risk. The increase comes from splitting
`SignatureLowerer` into an owned continuation plus borrowed driver, retaining one stable immutable
requirement allocation/cursor, and auditing early parameter preparation without changing solver
semantics. Slice 1 still must not change SCC readiness or delay production edges.

Slice 1 is divided further:

1. **Slice 1a: production binder bridge.** Move the test-only annotation bridge into the
   crate-private `RoleImplConformanceBinderBridge`, retaining separate logical `U` and `A` entries
   even when their same-session `TypeVar` overlaps. Add missing/ambiguous structured failures. Size
   S-M, risk medium.
2. **Slice 1b: owned signature-lowering continuation.** Refactor `SignatureLowerer` state out of its
   arena/module borrows; add stable immutable requirement ownership and a borrow-free spine cursor;
   prove method-local variables, closed rows, private tails, and the captured level survive one
   pause/resume. The production call path remains immediate. Size M, risk high.
3. **Slice 1c: inactive pending descriptor and parameter audit.** Capture anchors, already-prepared
   parameter uppers, the not-yet-lowered body cursor, continuation, separate deferred final metadata,
   and `RequirementParameterContextStatus` behind an inactive path. A conservative structural scan
   is the positive basis for `Clean`; existing bounds/subtract facts/epoch reads only provide a
   negative mutation audit. Never filter or retract facts. Effect-bearing parameter mutation is
   `Unavailable` until section 13 point 2 is decided. Size M, risk high.

Slice 1 exit requires all three sub-slices, unchanged immediate production output, and witnesses
showing that no body result/effect expected node is allocated before the conceptual snapshot point.
If stable row identity cannot be retained without changing serialized `SignatureType`, or if a
valid receiver body requires effect-bearing parameter context that cannot safely be classified,
stop before Slice 2 and return to the user and Claude Sonnet 5. Do not replace the continuation with
fact-level tagged subtraction as a local workaround.

### Slice 2: SCC conformance blocker

Size M, risk high. Add distinct pending/released inputs, component merge handling, ready-except-
conformance query, transition counters, and isolated SCC unit tests. Do not delay real edges yet.

### Slice 3: receiverless delayed connection shadow

Size M. Delay the single whole-method connection, capture a first-order read-only actual view,
apply the edge, settle, and release. Compare production outputs with the immediate baseline.

### Slice 4: receiver parameter/body split

Size M-L, risk very high. Split contextual parameter preparation from deferred body/final
connection. Cover zero/multiple parameters and result/effect annotations.

Slice 4c is paused after its zero-tail receiver shadow attempt exposed the binding-transaction
boundary gap recorded as section 13 point 10. The delayed path cannot be activated for receiver
methods until that point is resolved: matching diagnostics alone is insufficient when the delayed
method retains a scheme and runtime body that the immediate path rejects before `finish_binding`.
The incomplete Slice 4c implementation was discarded and the implementation returned to the
completed Slice 4b state (`661d7a66`).

### Slice 5: component-atomic recursion and merge witnesses

Size M-L. Exercise mutual SCCs, post-edge merges, recursive binders, failure release, and strict
transition bounds. Unsupported structures remain fail-closed.

### Slice 6: Stage 2 actual first-order view handoff

Size M. Move successful snapshots into the immutable conformance contract/output, connect the
already-defined declared view, and complete the first-order actual-side Exit witnesses. Do not add
the comparison/subsumption kernel.

No slice may silently broaden from explicit-complete source impls to inferred/partial associated
assignments.

## 13. Unconfirmed decisions and implementation blockers

The following remain unconfirmed and must be resolved or bounded by the relevant slice:

1. Whether a read-only compact view at ordinary SCC quiescence is complete enough for every
   first-order Stage 0 fixture without running mutating generalization prepasses.
2. Which requirement parameter constraints are legitimate contextual inputs versus claims that
   must also be deferred for universal conformance.
3. Whether lowering an expected signature into temporary upper nodes mutates shared bridge
   variables even before those uppers are connected; the initial split must test this directly.
4. How post-drain capture failures are routed into source diagnostics without changing legacy
   shadow behavior.
5. Whether delayed connection changes constraint insertion order observably in existing valid std
   impls.
6. Whether any expected-type-directed method selection is legitimate in a conforming impl body.
7. How inferred/partial associated ownership coordinates methods in separate SCC components.
8. Whether a future component-level hook in the single existing generalization pipeline is needed
   for records, effects, recursive bounds, predicates, or casts.
9. Whether transient candidates can use a pending method before its conformance snapshot exists;
   this is the parent specification's candidate-visibility question and remains unresolved.
10. How a deferred receiver requirement preserves the immediate path's binding transaction on
    connection failure. Slice 4c reproduced this with the following shape mismatch (shown compactly):

    ```yu
    role Build 'subject:
      our x.build: int
    impl int: Build:
      our x.build = \value -> value
    ```

    The declared result is non-function `int`, while the body is a lambda. Both paths report the
    same `SignatureTypeMismatch`, but their final definition states diverge. The immediate path
    detects the mismatch inside method lowering, before `finish_binding` can run, so the definition
    becomes `never = <missing>` and is included in `bodyless_decls`. The delayed path calls
    `finish_binding` first and detects the failed conformance connection only in the later pending
    phase. It therefore retains the body's real inferred scheme (for this fixture, a shape such as
    `int -> 'a -> 'a`) and lambda runtime IR, then merely adds the separate diagnostic; its
    `bodyless_decls` count also differs.

    This is a structural ordering problem, not a presentation difference. The invalid delayed
    definition remains usable as though it had a valid scheme, so another definition -- including
    a mutually recursive binding -- could observe and rely on a type that must not exist. Treat the
    gap as a soundness issue.

    Two candidate directions remain open:

    - **(a) Provisional binding transaction.** Keep the target method body provisional until its
      pending connection completes. On failure, commit the same `never = <missing>` state as the
      immediate path; on success, commit the body normally. This represents the failure exactly,
      but it expands the pending lifecycle from constraint edges into binding ownership. Depending
      on what must remain visible for recursive SCC construction, it may require delaying or
      splitting `finish_binding`, `DefFinished`, poly/typing writes, and ordinary quantification.
      Its interaction with mutual recursion and component merge is therefore broad and high-risk.
    - **(b) Stronger eager read-only pre-check.** Strengthen
      `check_impl_method_requirement_shape` or an equivalent pre-check so a body/requirement shape
      mismatch is detected before deferral. Such a method falls back to the complete immediate
      path and preserves the existing binding transaction while narrowing Slice 4c's blast radius.
      This is smaller and keeps SCC ownership unchanged, but it is not yet known whether a read-only
      pre-check can cover every connection failure class. In particular, value-type mismatches and
      failures that require settled bounds may remain invisible even if simple shape mismatches are
      excluded.

    Slice 4c (real SCC activation for receiver methods) cannot complete until this choice, or an
    equivalently sound transaction design, is resolved and witnessed against the immediate path.

11. Whether the already-active receiverless Slice 3 path also requires provisional binding
    publication for failures discovered only after deferral. Receiverless lowering has the same
    unconditional-call structure that exposed point 10: once deferred body lowering returns
    `Ok`, `lower_role_impl_method_binding` calls `finish_binding` and publishes the body, root edge,
    fetch, and possible runtime root before the pending-phase connection's success or failure is
    known.

    The concrete source-level shape/concrete-type mismatch class from point 10 is nevertheless
    independently safe on the receiverless path. Before constructing its deferred descriptor,
    `lower_impl_method_body_expr` runs `check_impl_method_requirement_shape` followed by
    `check_impl_method_requirement_concrete_type`. Either failure returns `Err` before
    `finish_binding`; the registered definition follows the ordinary failed-binding path and its
    unconnected root compacts to Bottom. This was verified by running the following counterexample:

    ```yu
    role Foo 'subject:
      our compute: int
    impl Foo int:
      our compute = \x -> x
    ```

    It reports `SignatureShapeMismatch` and finishes as `never = <missing>`, matching the immediate
    path rather than retaining the lambda's inferred scheme. Thus receiverless methods do not
    reproduce point 10 for the source mismatch class which triggered the receiver transaction
    work.

    A narrower residual gap remains. Receiverless Slice 3 does not own a
    `ProvisionalBindingCommit`, so a failure which passes both eager read-only checks but arises
    only while the pending phase resumes the saved continuation -- for example a
    `SignatureConstraint` error or internal descriptor corruption -- would occur after the binding
    publications above. No production source counterexample reaching such a late failure within
    the current explicit-complete, first-order blast radius has been found, but reachability has
    not been proved impossible either.

    If a reachable counterexample is found, the expected repair is to generalize the Slice 4c-T1/T2
    `finish_binding_provisionally` / `commit_provisional_binding` transaction to receiverless
    pending records, retaining the same single-`DefFinished`, component-atomic capture, settle, and
    release rules. Slice 4c deliberately does not make that extension. Deferring a known structural
    gap is not ideal from a soundness perspective, but without a reachable counterexample the extra
    production lifecycle change is not justified in this slice; the risk remains recorded rather
    than silently treated as impossible.

### 13.1 Point 10.1: provisional binding transaction detailed design

The user selected point 10 direction (a). Investigation of the current ownership boundaries makes
an implementation possible without rolling back solver state, but only if `finish_binding` is split
by publication responsibility. Delaying `DefFinished` itself is not the design: the existing
`first_component_ready_except_conformance` query requires every component member to be both
registered and finished. Withholding `DefFinished` from the pending method would therefore prevent
that method's component from ever reaching the phase which is supposed to settle it.

#### Current responsibilities and publication boundary

`lower_role_impl_method_binding` establishes the definition root before expression lowering. It
stores the root in `Typing`, registers the root with `SccInput::RegisterDef`, registers role-impl
ownership and requirement dependency metadata, and then lowers the body. Body lowering itself
emits resolved-use, selection, and dependency work needed to construct or merge SCC components.
None of those operations is performed by `finish_binding`.

On the successful path, `finish_binding` currently performs all of the following as one operation:

1. validate that the already-created poly definition is a `Def::Let`;
2. publish `computation.expr` as `Def::Let.body`;
3. connect `computation.value` as a lower bound of the registered definition root when
   `connect_body` is true;
4. derive and record `BindingFetch`, which also enqueues `SccInput::DefFetchRecorded`;
5. add `RuntimeRoot::ComputedDef(def)` for a computed binding when runtime roots are not
   suppressed; and
6. enqueue `SccInput::DefFinished`.

The scheme is not written by `finish_binding`. `DefFinished` only marks the member finished in the
open SCC component. Once every ordinary blocker and every conformance blocker is gone,
`QuantifyComponent` invokes the single production `quantify_component` path. That path writes the
generalized root into `AnalysisSession::schemes` and then writes the finalized `Scheme` into
`Def::Let.scheme`. `Typing` remains only the same-session `DefId -> TypeVar` table; it is populated
before body lowering even on a failed definition.

The provisional split classifies those operations as follows:

| Operation | Provisional timing | Reason |
| --- | --- | --- |
| `Typing::set_def`, `RegisterDef`, role ownership, requirement dependency | immediate, unchanged | Required to expose the definition root and construct the SCC graph. |
| Body lowering and its use/selection/dependency work | immediate, unchanged | Required to discover mutual recursion and component merges. |
| `ConformancePending` | before provisional `DefFinished` | Prevents the otherwise-finished component from quantifying. |
| `DefFinished` | immediate after the pending record is installed | Required by the ready-except-conformance query; it means lowering input is closed, not that the binding is valid. |
| `Def::Let.body = Some(expr)` | successful transaction commit only | A failed immediate method leaves `body = None`. |
| `computation.value <: def_root` | successful transaction commit only | This edge is monotonic and cannot be rolled back after a deferred failure. |
| `BindingFetch` and `DefFetchRecorded` | successful transaction commit only, before release | A failed immediate method records no fetch; success still establishes the generalization boundary and computed-fetch-cycle evidence before quantification. |
| `RuntimeRoot::ComputedDef` | successful transaction commit only | A rejected method must not remain executable runtime IR. |
| generalized/finalized scheme writes | ordinary `QuantifyComponent` only | The transaction must not introduce a second scheme owner or a second generalization pass. |

Result-annotation checks which already run from finalized schemes in `BodyLowerer::finish` are not
part of this transaction. Under current semantics they add a diagnostic without making a binding
bodyless. Only failures belonging to the legacy impl-requirement connection being deferred are
transaction success/failure inputs.

#### Exact immediate failure and poison equivalence

For the `Build` fixture in point 10, the receiver body and its raw value/effect anchors are lowered,
and the two legacy body requirement edges are prepared/applied before the final whole-method check.
`connect_impl_method_requirement` first calls `check_impl_method_requirement_shape` and then
`check_impl_method_requirement_concrete_type`. The observed `SignatureTypeMismatch` identifies the
second check as the rejecting function: in the compacted constructed method, the receiver result
still has the body's function shape where the corresponding requirement result is non-function.

The error propagates out of `lower_impl_method_body_expr`, so
`lower_role_impl_method_binding` calls `push_registered_expr_error` instead of `finish_binding`.
That records `BodyLoweringError::Expr` and calls `finish_failed_def`, whose only state transition is
`SccInput::DefFinished`. The module-map-created `Def::Let` therefore retains `body = None` and
`scheme = None`; the registered root receives no lower bound from the rejected body; no binding
fetch or computed runtime root is published. Ordinary SCC quantification subsequently compacts the
unconnected positive root to Bottom (`Never`) and writes the scheme, producing the observed
`never = <missing>`.

There is no current poison or rollback function to reuse. Poison equivalence is the absence of the
successful publications above, followed by the normal `DefFinished -> QuantifyComponent` path. An
implementation must not overwrite the root with a fresh variable, manufacture `Unknown`, or add an
explicit `Never` constraint. If other constraints legitimately reached the registered root before
failure, the target is the exact state produced by the immediate path for the same input, not an
unconditional syntactic `Never` scheme.

#### Proposed transaction representation and APIs

The pending conformance record should own a private, non-serialized, non-`Clone` transaction
payload. An illustrative shape is:

```rust
struct ProvisionalBindingCommit {
    def: DefId,
    name: Name,
    root: TypeVar,
    computation: Computation,
    connect_body: bool,
    publish_runtime_root: bool,
}

enum PendingBindingState {
    CapturedProvisional(ProvisionalBindingCommit),
    RequirementAppliedAndCommitted,
    RequirementFailedAndPoisoned,
}
```

`publish_runtime_root` captures `!suppress_runtime_roots` at the original lowering site; it must not
be recomputed later from whatever lowering mode happens to be active during the pending drain.
Although `Computation` is currently `Copy`, the wrapper and pending-table API must enforce single
consumption with `Option::take` or an equivalent state transition. Raw `TypeVar` and `ExprId`
members remain same-session transport metadata and are never serialized or treated as logical
conformance identities.

The implementation boundary should split the current helper into three responsibilities:

- an immediate wrapper which prepares and publishes the payload, then emits `DefFinished`,
  preserving every existing non-deferred call site;
- a provisional finish operation which validates the `Def::Let`, stores the payload in the pending
  record, and emits the one `DefFinished` without publishing body/root/fetch/runtime state; and
- a consuming commit operation which publishes body, body-to-root edge, fetch, and optional runtime
  root but does not emit a second `DefFinished`.

Deferred failure consumes and drops the payload, records the same `BodyLoweringError::Expr`, and
does not call `push_registered_expr_error`, because the provisional finish already emitted the
single `DefFinished`. A `Def::Let` validation failure is also terminal: record `NonLetDef`, discard
the payload, and release the conformance blocker. Re-enqueuing `DefFinished` would be set-idempotent
inside the SCC graph but would change lifecycle traces and obscure the one-transition invariant, so
it is not part of the design.

#### Component-atomic pending sequence

For a targeted receiver method, the lowering and pending phases become:

1. establish the public definition root and emit `RegisterDef` as today;
2. emit `ConformancePending` before the definition can become ready;
3. lower the body once, retaining its computation and completed receiver descriptor while emitting
   all ordinary dependency/use work;
4. install `ProvisionalBindingCommit` and emit the single `DefFinished`, without publishing its four
   commit-only effects;
5. at first ordinary quiescence, capture every pending member in the ready component before any
   deferred requirement edge or binding commit is applied;
6. consume each saved signature-lowering continuation in deterministic member order, resume the
   body expected layer, apply the two body edges and final legacy metadata/check exactly once, and
   use that legacy connection's `Result` as the transaction decision;
7. on success, consume and publish the binding payload, including `DefFetchRecorded`; on failure,
   consume and poison it by non-publication while recording the legacy diagnostic;
8. drain all resulting constraint, fetch, selection, and SCC work while the conformance blocker is
   still installed; and
9. at the next quiescence, release every member blocker and allow the ordinary component
   quantification path to run once.

Actual-view capture availability and binding validity are separate. Section 8.4 still requires the
legacy connection after a read-only capture returns `Unavailable`. If that connection succeeds, the
binding commits even though the shadow view is unavailable; if it fails, the binding is poisoned.
All member captures must precede both kinds of publication, including the body-to-root edge. The
component need not roll all member bodies back when one member fails: immediate semantics reject
definitions individually. However, commits and failures must occur only after the component-wide
capture batch, and their deterministic ordering needs a witness because legacy connection attempts
can themselves add monotonic constraints before returning.

#### Mutual recursion, component merge, and downstream visibility

The registered definition root remains the sole root used by `OpenUse`, so no second typing identity
is introduced. A provisional method may refer to ordinary or provisional peers during body
lowering, and those use edges still discover cycles and merge components. Component merge unions
the existing conformance-pending sets. A peer referring to the provisional method sees the open
public root, never a provisional scheme:

- successful commit adds the saved body value as a lower bound of that root before blocker release,
  so the bound propagates to every open use before joint quantification;
- failed commit omits that lower bound, just as the immediate error path does, so peers see only the
  constraints which could also have reached the failed registered root in the immediate execution;
  and
- no component member can observe a finalized scheme until every merged pending member has settled
  and released its blocker.

An incoming component which depends on the pending component remains behind its ordinary outgoing
SCC edge until the target component quantifies. An already-merged mutually recursive ordinary
binding is marked finished normally but cannot cause joint quantification while the conformance set
is non-empty. `DefFetchRecorded` is delayed only until successful commit: recording it before
release re-runs computed-fetch-cycle detection on the already-merged component and establishes the
correct value-restriction boundary before generalization. On failure it remains absent, matching
the current default `FetchValue` behavior for failed definitions.

This solves scheme visibility through the SCC/instantiate path. It does not by itself resolve point
9: a transient role candidate may have visibility outside ordinary scheme instantiation. Slice 4c
must retain that question as an independent fail-closed blast-radius condition.

#### Section 16 audit and boundedness

This proposal adds no inference fixed point. Each targeted definition has one of the following
finite paths, with no retry on capture or connection failure:

```text
CapturedProvisional -> RequirementAppliedAndCommitted -> Released
CapturedProvisional -> RequirementFailedAndPoisoned  -> Released
```

Component merge cannot reset a member state. The implementation must count provisional creation,
payload consumption, commit/poison, legacy edge application, and blocker release, and assert an
upper bound of one for each per method. It uses the existing single drain scheduler and the existing
single production quantification pass.

The saved body-to-root constraint is one delayed legacy edge, not a reversible constraint or a
protected variable. No provisional flag may be exposed to unification, floor, co-occurrence,
polarity simplification, or generalization; no rigid set, blocked pair, through marker, provenance
subtraction, or constraint rollback is allowed. If correctness appears to require a simplifier to
inspect provisional state, this design has failed and implementation must stop. Detached poly
expression nodes allocated while lowering a subsequently poisoned body are not made reachable
through `Def::Let.body` or a computed runtime root; exact arena/dump parity with the immediate error
path remains a required witness rather than an assumed property.

#### Size, risk, and required implementation slices

The total implementation is **L-XL, risk very high**, larger than the original Slice 4c estimate.
It changes the meaning boundary of `finish_binding`, pending orchestration, fetch timing, and
failure publication even though it must leave immediate call sites unchanged. Implement it only as
the following separately reviewed slices:

1. **Slice 4c-T1: structural binding-publication split (size S-M, risk medium).** Introduce the
   payload and commit helper, but have every production call prepare and commit immediately. Prove
   body, root bounds, fetch, runtime roots, `DefFinished`, scheme, diagnostics, and std totals are
   unchanged.
2. **Slice 4c-T2: inactive provisional transaction (size M, risk high).** Construct and consume the
   payload behind a test-only/inactive receiver path. Prove success publishes all four effects once,
   failure publishes none, and both paths emit exactly one `DefFinished`. Include computed-fetch and
   suppressed-runtime-root cases.
3. **Slice 4c-T3: zero-tail receiver activation (size M-L, risk very high).** Integrate the payload
   with component-atomic capture, saved continuation consumption, settle, and release. Fix the
   `Build` fixture against the immediate baseline and cover valid result annotations, pure/effect
   result anchors allowed by the existing blast radius, capture failure, connection failure, and
   internal descriptor failure.
4. **Slice 4c-T4: recursion and publication parity (size M-L, risk very high).** Cover receiverless
   plus receiver members in one component, a provisional receiver mutually recursive with an
   ordinary binding, component merge after use resolution, one success plus one poisoned member,
   computed-fetch-cycle diagnostics, candidate/selection/diagnostic parity, bodyless counts,
   schemes, runtime IR, and repository std totals.

Several details remain **to be verified**, not assumed: whether every deferred connection failure
class leaves the same partial anchor constraints as the immediate call order; whether detached
expression/local-definition arena entries are byte-for-byte or only reachability-equivalent on
failure; and whether candidate visibility in point 9 can observe a pending definition outside SCC
scheme instantiation. Any mismatch in these witnesses pauses activation before the next slice. Slice
4c remains paused until at least T1-T3 are separately implemented and reviewed; multiple-tail
receiver activation remains Slice 4d and must not be folded into this transaction work.

Slice 0 status update: point 3 is resolved as mutating for effect-bearing `U/A` and non-mutating only
for the characterized plain value-position cases. It remains numbered here as the historical
question that motivated the Slice 1 revision in section 5.1.1; it is no longer an open decision.
Point 2 remains open and blocks treating effect-bearing parameter preparation as valid actual-side
context.

These are not reasons to weaken the view or comparison. An unsupported case remains explicit and
blocks enforcement for that case.

## 14. Exit condition for the lifecycle project

The two-stage lifecycle is ready to serve Stage 2 actual views only when:

- the pending state machine is monotonic and bounded;
- every targeted component is snapshotted atomically before pending edges;
- all delayed-edge work settles before ordinary quantification;
- production generalization runs exactly once;
- immediate and delayed shadow outputs agree for valid non-enforced programs;
- malformed explicit-associated fixtures expose an unpolluted actual view;
- mutual recursion terminates without replay or unbounded unfolding;
- imported, cached, default, inferred-associated, and non-role paths retain documented behavior;
- failures release SCC blockers and produce structured evidence; and
- no Section 16 prohibition is bypassed under a different name.

Investigation and lifecycle specification design: Codex (gpt-5.6-sol), 2026-07-13 session. Whether
and when to implement remains a decision for Claude Sonnet 5 and the user; this document is a
feasibility and design specification, not an implementation commitment.

Reviewed and signed: Claude Sonnet 5, 2026-07-13. The blast-radius scoping (§7.1), the rejection of
a second generalization loop (§4, §9.2), and the Section 16 self-audit (§9) are sound as specified.
This signature approves the document as a reference specification only. It does not approve starting
any implementation slice; §12's slices, beginning with Slice 0, each require a separate go-ahead
given the very-high risk rating and the component-quantification machinery's incident history in
this repository (`label_sub.sub`, `once`).

Reviewed and signed (addendum): Claude Sonnet 5, 2026-07-13. Section 13.1's provisional binding
transaction design is sound as specified: keeping `DefFinished` immediate while deferring only
body/root-edge/fetch/runtime-root publication avoids the self-deadlock a naive reading of point 10
direction (a) would cause, and reusing the existing Bottom-compaction behavior for the failure case
(rather than inventing a new poison mechanism) keeps the change narrowly scoped. This signature
approves the section as a reference design only. Slice 4c-T1 (structural binding-publication split,
size S-M, risk medium) may proceed as the next implementation step under the same review discipline
as every prior slice; T2-T4 each still require their own review before implementation.

## Addendum (2026-07-15): candidate-independent fallback early-resolution project

This is a factual project-status record prepared by Codex under Claude's supervision. It is not a
new design decision and is not covered by the Claude signatures above.

### Problem and shipped proof surface

This sub-project addressed receiver methods such as `ParseError.merge` which use infix operators in
their bodies. The `.add` / `.lt` / `.gt` selections create SCC edges to unquantified
`std::core::ops::#op:infix:*` wrapper components. Those wrappers' own selections normally resolve
only in the late structured-method fallback batch, which runs after the conformance-readiness
check. The pending receiver therefore failed closed as `Unavailable(OrdinarySccBlocker)` before
the first-order actual-shape classifier could run.

Slices 1-6 shipped as test-gated proof infrastructure with zero production behavior change:

- `db7c72a8` exposed the shared role-solver readiness predicates.
- `ef85da02` added a deterministic, read-only SCC frontier query.
- `7f51e22d` added a fail-closed classifier which proves selection-level and component-level
  soundness by read-only projection, without scheme instantiation.
- `ce76bc49` split structured fallback collection from application without changing behavior.
- `075d34d7` added a test-only early-resolution driver toggle.
- `48d7b22a` proved the path against the real repository std. `ParseError.merge` advances to
  `Unavailable(NonAtomicSurface)`, not `Conforms`: the result is further classification, not full
  resolution. The complete census found 21 infix-using methods and 7 genuinely helped methods.

All of this remains behind `#[cfg(test)]`. The real-std proof also pins unchanged production
`output.errors`, the `998/3/297/0` std-comparison baseline, and production output parity.

Section 13 point 9 remains an open concern in the general lifecycle design. For the classifier's
narrow eligible subset, however, the relevant candidate-visibility concern is bounded: every
selection and component is checked all-or-nothing, the target must already be locally quantified,
and the read-only projected demands must remain unresolvable both before and after coalescing.
Imported, pending, ambiguous, locally shadowed, merge-requiring, or otherwise unsupported cases
fail closed. This proof does not settle candidate visibility outside that subset.

### Production activation investigated and deferred

Slice 7 attempted to make the proven early-resolution path part of unconditional production
scheduling. Three implementations preserved semantic parity but failed the performance acceptance
bar on `check-poly-std examples/showcase.yu`:

1. naive unconditional wiring: approximately **+46%**;
2. combined-quiescence gating: approximately **+11-14%**; and
3. demand-driven targeted triggering: approximately **+15-18%**, with no improvement over the
   combined-quiescence approach.

Each attempt retained byte-identical `dump-poly-std` output, the unchanged `998/3/297/0`
std-comparison baseline, identical `output.errors`, and the same 7/21 census result. The attempts
were therefore semantically viable but operationally non-viable and were deliberately not shipped.

Direct measurement localized the regression to role-solver scheduling. Every role pass rebuilds
method taint from all unresolved selections and rescans all candidates from scratch; there is no
incremental or dirty-tracking mechanism. At the natural late-fallback point, around round 161 of
approximately 176-190 total rounds, a newly resolved wrapper demand survives about 5 rescan rounds.
Resolving it early makes that same demand survive 14-21 rounds. Extending the demand's lifetime is
inherent in early resolution, so changing the trigger point within this project's scope cannot
remove the repeated work.

Production activation is therefore deferred. A future, separate project would first need a
role-solver incremental scheduling mechanism, such as dirty-owner or epoch-based invalidation, so
unchanged role demands are not rebuilt and rescanned every round. This addendum records that open
follow-up without designing it.

Status addendum: Codex (gpt-5.6-sol), 2026-07-15.
