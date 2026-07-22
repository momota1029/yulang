# Predictive suffix-safety oracle specification

Date: 2026-07-15

Status: **abandoned after Stage 0 falsified the predictive-oracle hypothesis (2026-07-15).** No
production oracle was activated; this document remains the historical design record.

## 1. Purpose

The suffix-safety oracle decides whether one specific suffix may reuse a cached std prefix without
running a full cold compilation first.

For prefix `P`, suffix `S`, and canonical compiled prefix artifact `C(P)`, a positive decision must
establish the following implication:

```text
oracle(C(P), S) = ProvenSafe(certificate)
  => suffix_interface(cold(P + S))
       ≡α suffix_interface(warm(C(P), S))
```

`≡α` is structural type-interface alpha-equivalence. It includes binder sharing and lifetime,
residual role predicates, recursive and stack binders, and the suffix-visible role-candidate
interface. Runtime-output equality is an additional regression witness, not the safety contract.

The immediate success condition is deliberately asymmetric:

- Yumark Markdown must be proved safe and take an explicit `std-prefix-hit` route.
- Yumark HTML must never be classified safe while its cold and warm interfaces differ. It may be
  classified `ProvenUnsafe` or conservatively `Unproven`; both results take the cold route.

This project exists because a completed warm compilation cannot validate its own safety. Forced
warm HTML compilation succeeds with no diagnostic while producing a non-alpha-equivalent `proof`
scheme. There is no error to catch after the fact.

The oracle is predictive in the following precise sense:

- it may parse, resolve, and shallow-lower the suffix;
- it may inspect a bounded proof summary stored with the prefix artifact;
- it may build read-only structural views and a compatibility certificate;
- it must not compile the prefix source again;
- it must not run cold whole-program generalization, finalization, specialization, or execution;
- it must not run the warm suffix through the divergent generalization/recursive-role-resolution
  phase before deciding that reuse is safe.

## 2. Verified current state and repository drift

### 2.1 Facts that still match the earlier design

The current code confirms the following pipeline facts:

1. `crates/yulang/src/std_prefix_cache_safety.rs` is still the production reuse gate. It first
   reloads the suffix with the cached syntax prefix, scans suffix CST for an `impl` containing a
   `where` clause, and only then scans finalized prefix schemes and candidates for an open role
   boundary.
2. The gate is a coarse correlation, not a proof about the actual prefix definitions or role
   candidates used by this suffix. It does not consume `CompiledBoundaryInterface` as a binder
   namespace and does not model `OpenUse` versus `InstantiateUse`.
3. `seed_imported_boundary` in `crates/infer/src/instantiate.rs` allocates and seeds only persisted
   unit boundary binders `B`. With a genuinely empty table it creates no shared open variable.
   Imported scheme `Q/R` binders are still freshened per use and imported candidates are freshened
   independently except for any actual `B` mapping.
4. `crates/infer/src/interface_oracle/closure.rs` is a read-only closure scanner over finalized
   `poly` structures. `alpha.rs` builds a structural view with disjoint per-use, boundary, and stack
   binder namespaces.
5. The top-level cold/warm oracle in `crates/yulang/tests/cli.rs` still runs both complete builds.
   Candidate comparison is not a first-class `interface_oracle` API; the test constructs a
   synthetic scheme containing candidate head, prerequisites, and method schemes.
6. The existing characterization test fixes the relevant result: HTML is non-alpha-equivalent and
   has `(cold, warm) = (56, 0)` closure violations for `proof`; Markdown is alpha-equivalent with
   `(0, 0)`.

### 2.2 Facts newer than the checked-in progress prose

Commits `881e8eab`, `9c346b65`, and `e7c845f7` repaired real candidate-freeze blockers. The current
investigation reports that repository std now completes the canonical handoff and emits a
structurally valid empty `B` table. Instrumentation established that zero entries means no actual
boundary-owned variable survives, not a silent writer fallback.

This result changes the interpretation of the remaining failure. `B = 0` is a valid statement
about the finalized prefix interface. It does not prove that finalizing std before this suffix is
observationally equivalent to letting the same suffix attach to still-open std definitions in a
cold build.

The checked-in prose has drifted behind that result:

- `notes/progress/daily/2026-07-15.md` currently contains the candidate-independent fallback
  closeout only; it does not record the later forced-warm HTML experiment or the successful empty
  canonical handoff.
- the later section of `tasks/current.md` still describes the repository artifact as a legacy
  empty fallback blocked by the `Index` candidate, even though the three commits above supersede
  that state;
- some Stage 6 CLI characterization assertions still expect the earlier handoff failure;
- the active cache format at HEAD is 19, not 20.

There is one stash named `WIP: format-20 marker-only safety gate (unsafe for HTML, superseded by
suffix-oracle design)`. It adds a canonical-handoff success marker and replaces the program-
sensitive gate with that marker. The forced-warm HTML result refutes that policy: a successful
canonical handoff is necessary but not sufficient for suffix safety.

This specification treats the supplied forced-warm observation as current-session evidence. It
does not silently rewrite the stale progress files because this task permits exactly one new
design document.

## 3. Terminology and safety result

The three binder classes from the canonical cache interface remain unchanged:

- `Q`: ordinary scheme quantifiers, fresh per use;
- `R`: recursive scheme binders, fresh per use;
- `B`: actual compiled-unit boundary binders, fresh once per imported analysis session and shared.

This project introduces a fourth proof-only class:

- `O`: counterfactual cold-open binders. These identify prefix definition roots and reachable
  inference variables that a suffix would have seen through `OpenUse` before prefix quantification
  in a whole-program cold build.

`O` is not a new Yulang type binder and must never be seeded into production warm inference. It is
metadata used by the safety proof. It must not be added to `CompiledBoundaryInterface`, treated as
`B`, marked rigid, or consulted by ordinary unification/simplification.

The public logical verdict is:

```rust
enum SuffixSafetyVerdict {
    ProvenSafe(SuffixSafetyCertificate),
    ProvenUnsafe(SuffixSafetyDifference),
    Unproven(SuffixSafetyUnavailable),
}
```

The names are illustrative. `Unproven` is intentionally not named `Unknown`, because Yulang's
`Unknown` is the only unknown *type*. An oracle classification must not blur that type-system
meaning.

Only `ProvenSafe` permits warm reuse. Both other outcomes take the existing full cold route. An
oracle limitation is a cache miss, not a source diagnostic.

For version 1, the observation set is broader than public exported schemes. It contains every
suffix definition reachable from a runtime root, exported value, suffix-visible candidate method,
selection/cast table entry, or another observed suffix definition. Private helper schemes can
change a later public result and therefore cannot be omitted merely because they are not exported.

## 4. Why existing mechanisms are insufficient

### 4.1 Canonical closure and `B` do not answer a suffix-specific question

The canonical cache interface proves that the finalized prefix artifact is structurally closed
under `Q/R/B` and that typed/runtime copies agree. It does not prove this commuting property:

```text
attach suffix uses to open prefix roots, then generalize
  ==
generalize prefix roots, instantiate them, then attach suffix uses
```

HTML is the counterexample. The finalized artifact can be completely valid and have `B = 0`, while
the two orders still produce different suffix role topology.

### 4.2 Runtime equality is too weak

HTML's current runtime output happens to match after ignoring timestamps, but the `proof` scheme
does not. Future uses, diagnostics, specialization decisions, or newly visible candidates can
observe that difference. Runtime equality cannot certify the cache boundary.

### 4.3 Speculative warm completion cannot fail closed

The forced HTML route exits successfully and emits no error. A design of “try warm, catch an error,
then compile cold” has no trigger and is unsound. A warm compile error may still cause an ordinary
fallback for availability, but that fallback is not a suffix-safety proof.

### 4.4 CST and name-resolution scans are necessary but not sufficient

The current `impl ... where` scan observes one syntactic hazard. Markdown and HTML fixtures are
otherwise structurally paired and differ at the final use of their typed document pipeline. The
actual distinction depends on resolved definitions, inferred sharing, interval openness, and role
input concrete-readiness. A new independent CST type approximator would duplicate lowering rules
and drift from the compiler.

### 4.5 The existing alpha oracle is an offline verifier, not the predictor

`SchemeAlphaView` remains the authoritative *notion* of structural equality for completed
interfaces. Its current top-level use needs both completed builds and therefore cannot be placed in
the production gate unchanged. Its traversal and binder-aware node vocabulary are reusable below,
but the predictive proof needs different inputs.

## 5. Architecture overview

The proposed architecture compares two bounded, shallow views of the same suffix before either
world generalizes the suffix:

```text
prefix artifact construction
  prefix bodies lowered, before whole-prefix drain/generalization
        |
        +-- capture proof-only CounterfactualColdInterface (`O` frontier)
        |
        +-- ordinary canonical finalize -> Q/R/B artifact
        |
        +-- persist handoff marker + cold frontier + fingerprints

reuse decision
  parse/load suffix once + build reusable pass-1/module state
        |
        +-- cold-frontier shallow probe --+
        |                                  |
        +-- canonical warm shallow probe --+--> SuffixUseInterface comparison
                                               |
                            ProvenSafe ---------+--> resume the warm probe
                            otherwise ----------+--> discard probes; full cold route
```

The probes use existing suffix lowering machinery through a new resumable cutoff. They do not run
prefix source lowering. They stop before ordinary suffix component quantification, generalization,
recursive role discharge, final poly freeze, specialization, or runtime execution.

This is intentionally not a marker-only gate and not a complete second compiler. The cold-frontier
probe exists only to produce a proof view. It can never supply user-visible compiled output.

## 6. Prefix-side counterfactual cold facts

### 6.1 Logical representation

The new artifact-level proof surface is conceptually:

```rust
struct CompiledSuffixSafetyInterface {
    capture_version: u32,
    canonical_handoff: CanonicalHandoffStatus,
    ports: Vec<ColdUsePort>,
    frontier: ColdFrontierGraph,
    candidates: Vec<ColdCandidateComponent>,
    coverage: SafetyFeatureCoverage,
}

struct ColdUsePort {
    stable_symbol: CompiledPrefixSymbol,
    component: ColdComponentId,
    root: ColdBinderId,
    warm_scheme: CanonicalSchemeKey,
}

struct ColdFrontierGraph {
    components: Vec<ColdOpenComponent>,
    binders: Vec<ColdOpenBinder>,
    type_nodes: CanonicalTypeDag,
    subtype_edges: Vec<ColdSubtypeEdge>,
    role_demands: Vec<ColdRoleDemand>,
    pending_work: Vec<ColdPendingWork>,
}
```

Names are illustrative. The required semantic content is:

1. Stable attachment ports for every prefix value, constructor, method, cast, effect operation,
   and role surface that suffix lowering can resolve.
2. Open definition roots and SCC component membership as observed before prefix quantification.
3. Every lower/upper interval, exact variable equality/share, stack/subtract identity, and type
   level reachable from those roots.
4. Pending selection, role-demand, reference, and SCC work that can change the reachable slice.
5. Candidate heads, associated values, prerequisites, and method references visible to suffix role
   resolution through their separate candidate capture path.
6. A coverage record saying which node/work kinds were represented. Missing or unsupported kinds
   make the summary unavailable; they do not disappear from the graph.

The graph is a transitive dependency slice from suffix-addressable ports, not a copy of every
unrelated inference allocation. A slice is valid only if every outgoing dependency is either
included or proven closed and irrelevant. Failure to close the slice makes the artifact
`Unproven` for suffix reuse.

### 6.2 Capture phase

The semantically faithful capture point is after prefix declaration/body/synthetic-body lowering
has generated its constraints, but before `drain_analysis_with_conformance` can quantify any
component. This matches cold whole-program ordering: all prefix and suffix bodies are lowered before
the ordinary global drain.

Capturing after prefix-only generalization would be too late; it would merely restate the finalized
artifact. Capturing each component independently as it quantifies is also not assumed equivalent,
because earlier quantification may affect later prefix work and insertion order has not been proved
irrelevant for this purpose.

The capture must be a read-only finite worklist over existing state. It must not settle, replay, or
protect a variable. The prefix compilation then continues through its unchanged ordinary drain and
canonical handoff. The proof surface and canonical artifact are two observations of one prefix
compilation, not two competing owners of inference state.

Current `compiled_unit_artifact_from_lowering` receives only completed `BodyLowering`, so this
requires an explicit lowering handoff carrying the earlier proof snapshot to the writer. Rebuilding
it later from finalized `poly` data is forbidden.

### 6.3 Difference from `B`

`B` answers “which variable remains genuinely unit-owned and shared after canonical finalization?”
`O` answers “which still-open prefix fact could a cold suffix have attached to before that
finalization?”

For real std, `B` can correctly be empty while `O` is non-empty. Promoting all `O` to `B` would
change warm inference semantics and recreate the protection/serialization approach rejected by the
canonical-interface design. The oracle instead checks whether this suffix can *observe* the
difference.

### 6.4 Artifact placement and format

The counterfactual surface belongs once on `CachedCompiledUnitArtifact`, as a sibling of syntax,
namespace, lowering, typed, and runtime surfaces. It should use an independently canonicalized DAG
instead of raw infer `TypeVar`, arena node, or `DefId` values.

The manifest needs:

- canonical-handoff success/fallback status;
- suffix-safety capture version;
- suffix-safety structural fingerprint;
- coverage/availability status;
- encoded size/node counts for budget validation.

Typed/runtime surfaces continue to carry the real `CompiledBoundaryInterface`; the proof surface is
not duplicated between them. Decode validates its own closure and fingerprint, and validates every
port against the namespace/runtime definition correspondence.

The next landed compiled-unit format bump should contain both the handoff marker and the actual
proof surface. The stashed marker-only format 20 must not land as the safety policy. If no other
format bump intervenes, this combined schema can use format 20; otherwise it uses the then-current
format plus one. Every older or marker-only artifact is a safe miss for this oracle.

Version 1 targets one repository std-prefix artifact. Merged general compiled-unit prefixes do not
receive a certificate by concatenation. They remain `Unproven` until disjoint frontier remap and
cross-unit port closure have their own witnesses.

## 7. Suffix-use interface

### 7.1 Derivation phase

The suffix-use interface is derived from partial/shallow lowering, not from a standalone CST walk.
The intended cutoff is:

```text
load suffix with cached syntax prefix
  -> build/append module-table pass 1
  -> register suffix declarations and lower suffix bodies
  -> capture generated use/constraint/role/candidate graph
  -> STOP before global drain, component quantification, and generalization
```

Stage 0 must characterize whether a small bounded amount of already-queued non-quantification work
must be routed to expose the decisive graph. If so, that work needs an explicit whitelist and hard
bound. The probe may not quietly become “drain everything except the last function call.”

The current `lower_loaded_files_with_prefix` entrypoint must be split into a resumable internal
lifecycle:

```rust
prepare_suffix_with_prefix(...)
    -> PreparedSuffixLowering

PreparedSuffixLowering::safety_view(...)
    -> SuffixUseInterface

PreparedSuffixLowering::resume()
    -> BodyLowering
```

The warm probe is retained and resumed after `ProvenSafe`; suffix body lowering is not repeated on
the successful cache path. The counterfactual probe is always discarded. On a non-safe verdict,
both are discarded and the existing cold builder starts from source.

Parsing and header/module loading are performed once and shared by both probes. Initially, the two
mutable analysis sessions may each lower the suffix body because their prefix use semantics differ.
A new route-neutral HIR solely to avoid this duplication is out of scope for version 1; introducing
one would turn the cache project into a front-end rewrite.

### 7.2 Logical contents

After raw session IDs are alpha-normalized, one `SuffixUseInterface` contains:

```rust
struct SuffixUseInterface {
    prefix_uses: Vec<ImportedUseAttachment>,
    suffix_roots: Vec<SuffixRootView>,
    constraints: CanonicalConstraintGraph,
    role_demands: Vec<SuffixRoleDemand>,
    candidates: Vec<SuffixCandidateView>,
    selections: Vec<SuffixSelectionView>,
    casts: Vec<SuffixCastView>,
    effects: Vec<SuffixEffectView>,
    pending_work: Vec<SuffixPendingWork>,
    coverage: SafetyFeatureCoverage,
}
```

It records at least:

- which stable prefix port each reference resolved to;
- use occurrence identity and the cold-open or warm per-use binder mapping;
- suffix-local definition roots and their reachable lower/upper graphs;
- equality/sharing classes, polarity, type levels, and stack/subtract binders;
- residual and pending role demands, with resolved role identity, inputs, associated values, and
  whether each input is definitely concrete, definitely open, or unsupported;
- all suffix-created candidate heads, associated values, prerequisites, and method scheme roots;
- selections, casts, and effect operations capable of adding constraints after the cutoff;
- the complete pending-work inventory reachable from an observed suffix root.

Resolved identities come from `ModuleTable`, compiled namespace symbols, and imported definition
mapping. The inference algorithm must never branch on source path, fixture name, function name, or
rendered type text.

### 7.3 Boundedness and failure

Each graph node is visited once with memoized `Pos/Neg/Neu` and constraint identities. Recursive
graphs use finite SCC identities; they are not unfolded. Unsupported syntax or work kinds, missing
prefix ports, ambiguous canonical ordering, incomplete closure, and budget exhaustion set an
explicit `Unproven` reason.

Errors produced inside a discarded probe do not become user diagnostics. Version 1 does not issue
`ProvenSafe` for a suffix whose shallow probes already disagree on structured errors or encounter an
unsupported error state; it falls back to the ordinary cold compilation.

## 8. Compatibility algorithm

### 8.1 Inputs

For the same parsed suffix, derive:

```text
ColdUse  = derive(counterfactual cold-frontier seed, suffix)
WarmUse  = derive(canonical Q/R/B seed, suffix)
```

The comparator also receives the prefix port table, canonical scheme/candidate keys, and the
counterfactual `O` ownership graph.

### 8.2 Normalization

Both views are normalized without solver mutation:

1. Validate closure and feature coverage.
2. Collapse only proven exact variable equalities: bidirectional, unweighted variable-only edges.
   One-way subtyping, same shape, or matching source origin is not equality.
3. Assign deterministic binder namespaces:
   - `ColdOpen(component, ordinal)` for `O`;
   - `WarmPerUse(use, ordinal)` for `Q/R` instantiations;
   - `Boundary(ordinal)` for `B`;
   - `SuffixLocal(root, ordinal)` for suffix-owned variables;
   - independent stack/subtract binder namespaces.
4. Canonicalize ordered type structure and canonical set-like role/candidate collections.
5. Compute each node's structural key once. Do not sort production data with repeated
   `format!("{:?}", ...)` calls.

### 8.3 Open-use/instantiation bridge

Cold `O` and warm per-use binders are not equal by declaration. They may be related by a
generalization/instantiation commutation bridge only when all of these hold:

1. The cold-open binder is reachable through exactly one imported-use occurrence in the observed
   suffix slice, or every corresponding warm occurrence is explicitly shared through the same
   actual `B` binder.
2. The binder does not connect two suffix roots or candidate components that warm instantiation
   freshens independently.
3. Its complete reachable lower/upper, recursive, stack, and role-demand closure has a bijective
   warm counterpart after the bridge.
4. No suffix constraint narrows one side without the structurally corresponding constraint on the
   other side.
5. Role concrete-readiness is the same on both sides. In particular, a role input may not be
   definitely concrete in warm while remaining open in cold.
6. No pending selection, cast, effect, or candidate work can observe the binder under different
   visibility or ownership.

If any condition is false, the result is `ProvenUnsafe` when a concrete structural difference is
available, otherwise `Unproven`. The checker never repairs the graph by adding fresh variables,
quantifying an unmatched `O`, or deleting a role predicate.

### 8.4 Final checks and certificate

After applying only approved bridges, compare:

- every observed suffix root and its complete reachable constraint/role closure;
- binder sharing and split/merge topology;
- role demand paths, variance positions, inputs, associated types, and concrete-readiness;
- recursive and stack binder graphs;
- prefix-visible and suffix-created candidate heads, associated values, prerequisites, and method
  scheme roots;
- pending work capable of changing those views.

Equality is a bijection. Two cold variables may not map to one warm variable, and one shared cold
variable may not map to two warm variables.

`ProvenSafe` returns a certificate containing the artifact fingerprint, suffix source key, feature
coverage version, normalized view fingerprints, bridge map, and node/work counts. The certificate
is process-local for the current build; persisting per-suffix certificates is a later optimization.

The production oracle does not claim a complete decision procedure. It proves a sufficient
commutation condition. A safe program outside the supported proof domain compiles cold.

## 9. Reuse of `interface_oracle`

The existing code is reusable, but not as one unchanged top-level call.

Reusable pieces:

- `ClosureScan` already traverses every current `Pos`, `Neg`, `Neu`, role argument, associated type,
  and stack-family type argument without solver mutation.
- `AlphaPos`, `AlphaNeg`, `AlphaNeu`, role predicate, recursive-bound, boundary-bound, and stack
  representations cover the finalized structural vocabulary needed by the new graph views.
- separate binder namespaces and bijective structural equality are exactly the right discipline;
- `first_difference`-style witnesses are useful for shadow telemetry and regression failures.

Required refactoring/extensions:

- live inference bounds, subtype edges, type levels, SCC/open-root identities, and pending work are
  not represented today;
- `AlphaTypeBinder` needs proof-view namespaces for `O` and suffix-local variables;
- the current alpha builder consumes finalized `TypeArena` nodes, not a live `ConstraintMachine`
  slice;
- current unordered keys use debug strings and are suitable for tests, not the production hot path;
- candidate alpha comparison must become a first-class view instead of the CLI test's synthetic
  scheme convention;
- recursive/symmetric graph ambiguity must retain the existing conservative rejection policy unless
  a separately reviewed complete canonicalizer is introduced.

The completed cold/warm `interface_oracle` remains the acceptance oracle for the predictor in tests.
It does not run in a production reuse decision.

## 10. Explicit resolutions of the six decision points

These are proposed resolutions for review, not previously signed decisions.

### 10.1 Decision 1: safety contract

**Proposed resolution (2026-07-15): use type-interface alpha-equivalence, not runtime-output
equality.**

The contract includes all observed suffix scheme closures and suffix-visible candidate interfaces.
Runtime and diagnostic parity remain mandatory acceptance witnesses, but runtime equality cannot
turn a type-interface mismatch into a safe verdict. HTML demonstrates why.

### 10.2 Decision 2: unprovable suffixes

**Proposed resolution (2026-07-15): fail closed.**

Every unsupported feature, incomplete frontier slice, ambiguous mapping, budget excess, malformed
artifact, or proof-kernel limitation returns `Unproven` and takes the existing cold route. The
oracle is permitted to miss optimization opportunities; it is not permitted to guess safety.

### 10.3 Decision 3: suffix-use derivation phase

**Proposed resolution (2026-07-15): derive it from resumable partial lowering, after normal
name/declaration resolution and body constraint generation, before global drain/generalization.**

CST-only and name-resolution-only views lack inferred sharing and role input readiness. A separate
approximate type traversal would duplicate compiler semantics. The normal loader, module table,
annotation lowering, expression lowering, and constraint generation are reused. The safe warm probe
is resumed so this work is not duplicated on the successful path.

### 10.4 Decision 4: persisted prefix data

**Proposed resolution (2026-07-15): add a versioned counterfactual cold-frontier surface; the
format-20 handoff marker alone is insufficient.**

The new surface records `O` roots, reachable facts, pending work, ports, and candidate components at
the pre-drain attachment frontier. It is proof metadata distinct from `B`, hashed and closure-
validated in the artifact. The next format bump should land marker and proof surface together.

### 10.5 Decision 5: fail-closed budget

**Proposed resolution (2026-07-15): enforce structural hard caps and a measured activation budget;
budget exhaustion is `Unproven`, never speculative warm reuse.**

The algorithm must be linear/near-linear in captured frontier plus suffix-use slice, with every node
memoized and no generalization/role-solve fixed point. The safe path reuses parsing, pass 1, and its
warm shallow-lowering state. The unsafe path may waste at most the bounded probes before cold
fallback.

Production activation additionally requires all of these measured gates:

- oracle-only incremental time at p95 is at most 10% of the corresponding cold `build_poly` time;
- total Markdown safe-path time is at most 60% of its cold route in five alternating release-build
  rounds;
- the proof summary is at most 10% of the existing std compiled-unit artifact and passes a separate
  absolute size cap;
- no accepted fixture exceeds the configured node, edge, pending-work, or memory cap.

The exact absolute byte/node/time constants are not guessed in this specification; Stage 6 must
measure and propose them for explicit sign-off before activation. Until constants are approved, the
production verdict remains cold and the oracle can run only in tests/shadow telemetry.

### 10.6 Decision 6: comparison scope

**Proposed resolution (2026-07-15): compare schemes and suffix-visible role candidates through one
shared binder namespace.**

Candidate head/associated/prerequisite data is a separate capture path from ordinary schemes and can
change suffix role resolution independently. The scope also includes candidate method scheme roots
when they are reachable. Comparing schemes alone would repeat the gap already established by
canonical-interface Stages 0-4 and Oracle B.

## 11. Rejected alternatives

1. **Marker-only format 20.** Refuted by canonical-successful, empty-`B`, unsafe HTML.
2. **Speculative warm completion with error fallback.** Refuted by successful silent HTML
   divergence.
3. **Runtime-output hashing.** Does not observe the type-interface mismatch.
4. **Keep expanding the `impl ... where` CST heuristic.** Cannot express actual resolved use,
   sharing, or role concrete-readiness and invites fixture-shaped rules.
5. **Run the existing cold/warm oracle before every build.** Correct as a test oracle but erases the
   cache benefit.
6. **Treat every counterfactual `O` as `B`.** Changes production binder lifetime and turns proof
   metadata into a new inference protection mechanism.
7. **Serialize the entire `ConstraintMachine` and resume it as production output.** This is the old
   broad Option 2 with the largest state/compatibility burden. The proposed frontier is bounded,
   proof-only, and discardable; if its closure approaches the complete machine, the budget rejects
   it instead of silently broadening scope.
8. **Create a new CST/HIR type approximator.** Duplicates lowering semantics. A route-neutral HIR
   may be a future independent front-end project, not a prerequisite smuggled into this gate.

## 12. Staged implementation plan

Sizes use this project's `S / M / M-L / L / L-XL` review scale. Risk uses
`low / medium / medium-high / high / very-high`.

No stage may begin merely because it appears below. This draft itself needs Claude/user review.
“Decision-free” below means the slice can be considered pure characterization/scaffolding *after*
the design is accepted; it does not override the pending approval at the end of this document.

### Stage 0: decisive-frontier characterization

- Size: S-M.
- Risk: medium.
- Approval class: decision-free characterization.
- Changes: test-only event/phase traces for paired Markdown/HTML, the small Oracle B control, and
  ordinary non-role suffixes. Record prefix/suffix body-lowering cutoff, queued work, first
  cold/warm graph difference, generalization/role time, and forced-warm success/diagnostics.
- Production behavior: none.
- Exit criteria:
  1. forced warm HTML is fixed as exit-success/no-diagnostic/non-alpha-equivalent evidence;
  2. Markdown remains completed-interface alpha-equivalent;
  3. a pre-generalization frontier contains a structural signal that distinguishes the pair;
  4. suffix shallow-lowering cost is measured separately from drain/generalization;
  5. if no bounded pre-generalization signal exists, stop and revise this architecture before
     Stage 1.

### Stage 1: proof-view and first-class candidate scaffolding

- Size: M.
- Risk: medium-high.
- Approval class: decision-free scaffolding, test-only/no route change.
- Changes: factor `interface_oracle` node/binder/closure primitives so they can consume a generic
  structural graph; add efficient memoized structural keys and a first-class candidate alpha view.
- Production behavior: none; new code remains test/support-only at this stage.
- Exit criteria:
  1. existing scheme alpha tests remain unchanged;
  2. candidate views match Oracle B's current synthetic-scheme characterization;
  3. alpha rename passes and binder split/merge fails;
  4. symmetric/recursive ambiguity fails closed without permutation search;
  5. no debug-string sort remains in the proposed production key path.

### Stage 2: in-memory counterfactual cold-frontier capture

- Size: L.
- Risk: high.
- Approval class: explicit human sign-off before implementation.
- Changes: expose the prefix pre-drain capture seam, build a read-only transitive frontier slice,
  classify `O`, capture ports/pending work/candidates, and carry it in memory to tests. Do not
  serialize or change reuse decisions yet.
- Exit criteria:
  1. capture does not mutate constraints, SCC state, role tables, or quantification order;
  2. capture closure is complete or produces a structured unavailable reason;
  3. real std capture succeeds within recorded node/size bounds;
  4. prefix compiled schemes/candidates/diagnostics/runtime output are byte- or alpha-identical with
     capture disabled;
  5. no `O` is inserted into `B` or production inference.

### Stage 3: resumable shallow suffix lowering

- Size: L.
- Risk: very-high.
- Approval class: explicit human sign-off before implementation.
- Changes: split `lower_loaded_files_with_prefix` into prepare/shallow/resume phases; build canonical
  and counterfactual probe seeds; share loaded CST/pass-1 inputs; expose raw suffix-use graphs.
- Exit criteria:
  1. resuming the canonical probe produces the exact current warm output and timing counters;
  2. discarding either probe publishes no scheme, diagnostic, artifact, or runtime root;
  3. no component quantifies before the decision point;
  4. every suffix definition/use is lowered at most once on the accepted warm path;
  5. cold fallback still enters the unchanged full cold builder;
  6. malformed/unsupported probe states terminate as `Unproven` without deadlock.

### Stage 4: compatibility kernel in shadow mode

- Size: L.
- Risk: very-high.
- Approval class: explicit human sign-off before implementation.
- Changes: normalize the two `SuffixUseInterface` graphs, implement the `O`/per-use commutation
  bridge, compare role readiness and candidates, and emit certificates/differences. Test/shadow
  only; route remains unchanged.
- Exit criteria:
  1. Markdown yields `ProvenSafe`;
  2. HTML yields `ProvenUnsafe` or `Unproven`, never `ProvenSafe`;
  3. small Oracle B and non-role controls are safe;
  4. candidate-only and scheme-only adversarial differences are rejected;
  5. rename/module-move metamorphic tests keep the same verdict when resolution targets are the
     same;
  6. every shadow `ProvenSafe` case is completed cold/warm alpha-equivalent for schemes and
     candidates;
  7. no solver mutation, role search, or repeated simplify-until-stable loop exists in the kernel.

### Stage 5: artifact schema and fail-closed decode

- Size: M-L.
- Risk: high.
- Approval class: explicit human sign-off before implementation.
- Changes: add handoff marker, counterfactual surface, fingerprint/counts, format bump, writer,
  decoder, source-key/hash, and malformed/old-format tests.
- Exit criteria:
  1. canonical success-empty and legacy-empty fallback are distinguishable;
  2. marker-only/format-19/old/truncated artifacts are misses;
  3. missing ports, duplicate binders, fingerprint disagreement, incomplete coverage, and excessive
     encoded counts are misses;
  4. repository std round-trips the exact in-memory frontier view;
  5. merged artifacts remain unavailable in version 1 rather than inventing merge semantics.

### Stage 6: route-preserving production shadow and budget selection

- Size: M.
- Risk: high.
- Approval class: explicit human sign-off before implementation.
- Changes: run the production-shaped oracle behind shadow telemetry while preserving the current
  safety gate and route. Record verdict reason, graph counts, summary size, probe cost, comparator
  cost, and completed Oracle B result in tests/bench scripts.
- Exit criteria:
  1. zero false-safe results over repository tests, Yumark pair, role controls, and generated
     alpha/binder/candidate adversaries;
  2. Markdown is consistently predicted safe and HTML consistently non-safe;
  3. performance gates in Section 10.5 pass;
  4. explicit absolute caps are proposed from measurements and approved;
  5. route assertions prove shadow mode cannot turn a cold case warm.

### Stage 7: fail-closed production activation

- Size: M-L.
- Risk: very-high.
- Approval class: separate explicit human sign-off immediately before activation.
- Changes: make `ProvenSafe` the only std-prefix reuse authorization; resume the prepared warm
  lowering state; route `ProvenUnsafe`/`Unproven` to cold. Keep the old heuristic as shadow
  comparison for this stage.
- Exit criteria:
  1. Markdown explicitly reports `std-prefix-hit` and meets the performance gate;
  2. HTML explicitly reports `full-miss` before divergent generalization begins;
  3. completed cold/warm Oracle B remains alpha-equivalent for every accepted fixture, including
     candidates;
  4. runtime results and structured diagnostics match for accepted fixtures;
  5. instrumentation proves the production oracle never invokes full cold compilation to make a
     positive decision;
  6. any post-certificate invariant violation disables reuse and is treated as a compiler bug, not
     as a new speculative fallback policy.

### Stage 8: heuristic retirement and hardening

- Size: S-M.
- Risk: high.
- Approval class: separate explicit human sign-off after Stage 7 evidence.
- Changes: remove the suffix CST/open-role heuristic and marker-only policy remnants; retain
  canonical artifact validation, suffix certificate validation, metrics, and cold fallback.
- Exit criteria:
  1. no source-name/path/fixture-sensitive gate remains;
  2. all route tests assert exact hit/miss outcomes;
  3. stale/malformed/budget-exceeding artifacts remain safe misses;
  4. README progress is updated in the same future implementation change if native/cache behavior
     reporting is affected;
  5. the signed canonical-cache spec is amended only after Claude/user review to replace its old
     Stage 7 assumption that canonical closure alone retires the program-sensitive gate.

## 13. Acceptance oracles

### Oracle S0: silent-failure witness

Forced warm HTML completes successfully with no diagnostic but differs structurally from cold.
This prevents error fallback from being reintroduced later.

### Oracle S1: paired Yumark prediction

With the same repository std artifact and structurally paired sources:

- Markdown is `ProvenSafe`;
- HTML is not `ProvenSafe`;
- neither verdict depends on the names `html`, `markdown`, `proof`, the fixture path, or module path.

### Oracle S2: completed-interface confirmation

For every `ProvenSafe` fixture, run the existing offline full cold/warm Oracle B in tests and compare:

- every observed suffix scheme;
- suffix-visible candidates and method schemes;
- binder class/lifetime and sharing;
- role predicates, recursive bounds, boundary bounds, and stack binders;
- runtime result and structured diagnostics separately.

### Oracle S3: binder topology adversaries

Positive and negative fixtures cover:

- one cold `O` used once versus one warm `Q` instance;
- one cold `O` shared by two uses while warm freshens twice;
- a real shared `B` used by schemes and candidates;
- two cold variables incorrectly merged warm;
- one cold variable incorrectly split warm;
- recursive and stack binders;
- role input open in cold but concrete in warm.

### Oracle S4: candidate separation

Hold ordinary schemes equal while changing a suffix-visible candidate head, associated value,
prerequisite, or method scheme. The oracle must reject. Hold candidate interfaces equal under alpha
rename and accept when the remaining suffix graph also commutes.

### Oracle S5: fail-closed coverage and budget

Unknown node/work kinds, incomplete closure, ambiguous recursive graphs, corrupted fingerprints,
old formats, excessive count fields, and runtime budget exhaustion all route cold without a source
diagnostic.

### Oracle S6: no-full-cold positive decision

Test counters prove that `ProvenSafe` was produced before any call to the full cold builder and
before suffix generalization/recursive role resolution. The later offline Oracle B invocation is
test validation only.

## 14. Performance and no-heavy-fixpoint audit

The design is acceptable only under these constraints:

- prefix frontier capture is one reachability traversal with visited sets;
- each shallow probe lowers the suffix once and stops at a bounded frontier;
- the accepted warm probe is resumed, not rebuilt;
- graph normalization uses exact-equality SCCs and memoized structural keys once;
- recursive types are represented by finite binders/SCCs and never unfolded to stability;
- no candidate search occurs inside the comparator;
- no second generalization loop or “generalize only enough to predict” loop is introduced;
- no `O`, safety verdict, or capture marker is visible to unification, floor/co-occurrence,
  polarity elimination, or ordinary role resolution;
- no rigid/protected set, blocked pair, or through flag is added;
- no missing information is represented as `Any` or `Never`; incomplete proof state is an oracle
  `Unproven` result, outside the Yulang type lattice.

The most likely performance failure is not the structural comparator but frontier size or probe
work. If the dependency slice closes over most of std's live machine, or a shallow probe must run the
same recursive role search as full generalization, the design has missed its purpose. The correct
response is a budgeted cold fallback or architectural review, not raising the cap until the cache
appears to hit.

## 15. Diagnostics and telemetry

The oracle changes cache routing, not source semantics. `ProvenUnsafe` and `Unproven` are not user
type errors. Under timing/debug flags, telemetry should expose stable categories such as:

- canonical handoff unavailable;
- counterfactual frontier unavailable/incomplete;
- unsupported suffix feature/work kind;
- open/per-use sharing mismatch;
- interval mismatch;
- role concrete-readiness mismatch;
- candidate mismatch;
- recursive canonicalization ambiguity;
- artifact or runtime budget exceeded.

Raw `TypeVar`, arena node, `DefId`, source path, or fixture name may appear in a debug detail only;
they are not stable verdict keys. A concise structural first-difference witness should use canonical
binder and port IDs.

## 16. Rollback and compatibility

Stages 0-6 are characterization, scaffolding, artifact, or shadow work and must leave the production
route unchanged. Stage 7 is the first behavior change.

If activation produces one false-safe case:

1. disable the production positive verdict;
2. preserve the counterexample and completed Oracle B witness;
3. classify whether prefix capture, suffix-use capture, bridge rules, candidate scope, or artifact
   validation was incomplete;
4. do not add a path/name/fixture special case;
5. do not weaken alpha comparison or redefine runtime equality as safety;
6. retain shadow telemetry only if it cannot affect route or inference.

An unavailable or stale proof surface is compatible by becoming a cache miss. It must not make a
valid source program fail.

## 17. Unconfirmed points and implementation blockers

The following are genuine unknowns. They must remain explicit until the named stage resolves them.

1. **Exact counterfactual capture closure.** It is not yet proved which queued constraint, SCC,
   selection, role, reference, cast, and effect facts must accompany a pre-drain public-root slice.
   Stage 0 inventories the state; Stage 2 must fail capture if a dependency cannot be closed. A
   partial graph cannot be accepted as “probably enough.”
2. **Decisive shallow cutoff.** The proposed cutoff is after suffix body constraint generation and
   before global drain. It is unconfirmed whether the HTML/Markdown distinction is already visible
   there or requires a bounded subset of queued work. If the first decisive point requires suffix
   generalization or recursive role solving, the proposed predictor is not cheap enough and must be
   redesigned rather than silently extending the probe.
3. **Completeness of the commutation bridge.** The single-use/non-escaping `O` to warm-per-use rule
   is a conservative leading criterion. Stage 0/4 must prove it accepts Markdown and rejects HTML.
   Passing those two fixtures alone is not a universal proof; adversarial sharing, variance, role,
   recursive, effect, and candidate tests are mandatory.
4. **Prefix frontier size for real std.** The transitive suffix-addressable slice may approach the
   complete live inference state. If it exceeds the Section 10.5 size/performance gates, the
   artifact design is not viable in its current form. Do not compress away semantic facts to meet
   the target.
5. **Exact absolute budgets.** The fail-closed policy and relative activation gates are resolved,
   but absolute bytes, nodes, edges, pending-work entries, memory, and watchdog duration need Stage
   6 measurements and explicit human approval.
6. **Recursive graph equality.** The canonical-interface project chose conservative ambiguity
   rejection rather than a complete SCC canonicalizer. This specification carries that policy
   forward provisionally. Any need for a stronger algorithm is a separate design decision.
7. **Probe ordering equivalence.** Sharing parsed/pass-1 inputs while lowering two mutable suffix
   sessions is straightforward conceptually, but it is not proved that current lowering has no
   external publication or process-global observation before `finish`. Stage 3 must inventory and
   witness discard safety.
8. **Candidate method visibility boundary.** Version 1 includes reachable candidate method scheme
   roots. The exact stable correspondence for default/imported/private methods may require more
   metadata than the current Oracle B label-based test convention. Missing correspondence is
   `Unproven`, not permission to omit the method.
9. **General compiled-unit and merge support.** Version 1 is std-prefix-only. Extending certificates
   to merged source-unit prefixes requires disjoint `O` remap, port deduplication, cross-unit
   pending-work closure, and separate performance evidence.
10. **Formal congruence claim.** Structural equality of the complete observed shallow graph plus
    approved open/use bridges is intended to be a sufficient condition for identical later
    generalization. That congruence needs to be stated and reviewed against the actual generalizer
    before Stage 7. Empirical Oracle B coverage is necessary evidence, not a substitute for the
    invariant.

No implementation may resolve these points by unconditional quantification, `Any`, predicate
deletion, candidate-name matching, protected variables, or a new solver fixed point.

## 18. Overall size and risk

Overall estimate: **L-XL, risk very-high**.

Expected blast radius is approximately 12-20 files and 2,000-4,000 lines including structural
views, capture/import data, lifecycle split, artifact code, telemetry, fixtures, and adversarial
tests. The estimate is larger than a gate replacement because the sound decision needs both a
pre-generalization prefix proof surface and a resumable suffix-lowering frontier.

The very-high rating has four independent causes:

1. a false positive is silent and can change inferred interfaces without an error;
2. prefix capture touches the inference lifecycle before quantification;
3. suffix probing must pause and resume lowering without publishing partial results;
4. schemes and candidates have separate capture paths that must share one binder correspondence.

The project is still narrower than resuming the complete serialized `ConstraintMachine` as the
production compiler state. If Stage 2 shows that no closed smaller frontier exists, the estimate
must be revised upward and implementation must stop for another design decision.

## 19. Completion gates

The suffix-safety oracle project is complete only when:

- repository std canonical construction succeeds and its handoff marker is persisted;
- counterfactual frontier capture is closed, versioned, hashed, bounded, and independent of `B`;
- the suffix-use interface is derived through resumable existing lowering, not name/path heuristics;
- `ProvenSafe` is a binder-bijective structural certificate covering schemes and candidates;
- every unproved, malformed, unsupported, ambiguous, or over-budget case falls cold;
- Markdown takes an explicit warm std-prefix hit;
- HTML takes an explicit cold route before divergent generalization;
- every accepted fixture passes completed cold/warm scheme and candidate alpha-equivalence;
- runtime and structured diagnostics remain equal as secondary checks;
- the production positive decision runs no full cold compile;
- performance gates and approved absolute caps pass;
- no inference fixed point or simplification protection mechanism was added;
- the old CST/open-role heuristic is removed only after separate Stage 8 approval;
- the signed canonical-cache document is reviewed and amended to reflect the new suffix-sensitive
  proof boundary.

Investigation and design: Codex (gpt-5.6-sol), 2026-07-15 session.

Implementation approval is pending Claude/user review. This attribution records the investigation
and draft specification only; it is not a Claude signature and does not approve starting any
implementation stage.

---

**Reference-specification approval (2026-07-15): Claude Sonnet 5 and the user reviewed this document and accept it as the reference specification for the suffix-safety oracle project.** This approval covers the architecture, the six decision-point resolutions in Section 10, the rejected-alternatives list in Section 11, and the staged plan in Section 12 as the basis for future work. It does NOT constitute implementation approval for any stage — per Section 12's own text, every stage (including Stage 0) requires its own separate sign-off before implementation begins, and Stages 2 and later require explicit human sign-off individually. The project's own built-in early-exit conditions (Stage 0 exit criterion 5; the Section 18 note that Stage 2 findings may force a size/risk re-estimate) remain in force: if Stage 0 or Stage 1 characterization falsifies the core architectural hypothesis, this specification must be revised before any further stage proceeds, not patched around.

---
