# Frozen Oracle: ordinary application source-boundary producer

Date: 2026-10-07
Status: frozen bounded historical characterization; compiler-referee reviewed, minor wording findings repaired
Yulang3 baseline: `12dddeaf06ee1ca858d77b4f39f7e40baf3b3992`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Semantic and implementation authority: none
Method: read-only source trace; no Oracle execution

## Question and result

The open `ORIGINAL_ASSOC` source producer needs a query-independent source
interpretation of an ordinary application and its typed invocation incidence,
before comparison or projected evidence is used. The earlier
[source-boundary eligibility archaeology](2026-10-06-frozen-oracle-source-boundary-eligibility-mechanism.md)
already identified the historical producer. This focused reread adds the
per-argument CST-range construction and makes the origin-before-demand,
immediate-drain, span-after-demand order explicit; it is not a novel producer
discovery.

**Result:** the frozen Oracle has a concrete source-boundary producer. It
allocates an `ApplicationArgument` source origin before constructing the
callee's negative Function demand, passes that origin to the subtype request,
then conditionally associates the returned App expression with its source
application and callee spans. When source-span recording is enabled and all
three spans are available, it separately associates their triple with the
allocated source-boundary ID. This preserves a historical
source-application-to-demand route across an eager constraint submission.

The mechanism does not introduce the currently missing original
owner/view-kernel witness. In particular, the stored records have no
`beta`/`Slots(beta)`, formal owner, typed Function-path incidence, complete
Call contribution, original `xi=(nu,K,D)`, or exhaustive licensing relation.
It is useful evidence about where historical source identity entered the
ordinary application path, not evidence that the current source producer is
semantically determined by Oracle.

## Exact historical chain

All paths below are relative to the pinned Oracle checkout.

1. `crates/infer/src/lowering/expr/tail.rs:89–126` lowers each source
   application argument and calls `make_source_app`. In a multi-argument
   application it updates `callee_source_range` after each application, so
   each generated App has its own callee/application range and argument range.
   The final argument range may cover the complete CST application; the
   separately supplied `argument_boundary_source_range` is the argument
   expression's own range.
2. `tail.rs:630–642` allocates
   `ConstraintOriginKind::ApplicationArgument` and immediately passes its
   origin to `make_app_with_origin`.
3. `tail.rs:535–563` allocates result/call endpoints, builds the negative
   four-port `Neg::Fun { arg, arg_eff, ret_eff, ret }`, and submits
   `Pos::Var(callee.value) <: callee_upper` with that source origin. The
   constraint machine's `subtype` entry enqueues and drains (`constraints/
   machine/entry.rs:493–499`), so later source-span registration must retain
   the allocated identity across the submission boundary.
4. After the call returns, `tail.rs:643–667` inserts application and callee
   spans in `application_provenance`, keyed by the generated App `ExprId`,
   only when both `source_span` conversions succeed. With source-span recording
   enabled and all three spans available, `tail.rs:668–685` inserts a
   `SourceBoundaryProvenance` record keyed by the earlier `SourceBoundaryId`.
   The record's argument span is required; it is the whole record that may be
   absent. The zero-argument branch (`tail.rs:95–105`) supplies no argument
   span, and `expr/mod.rs:193–196` can disable span recording.
5. `constraints/machine/entry.rs:433–451` stores the source kind and boundary
   together with its `OriginId`. Thus the source-boundary table and expression
   provenance are separate records joined by the source call construction,
   not one semantic signature object. `constraints/explain.rs:2063–2084`
   preserves the `ApplicationArgument` origin/source-role category in portable
   explanations.

The producer submits the demand before installing the source-span records.
This is a clear temporal/identity-plumbing mechanism: a stable origin ID is
allocated first, carried into the submitted relation, and used to attach
source coordinates afterward. It does not show that solver results determine
the source coordinates.

## Correspondence and limit

| Historical record | What it identifies | Missing current source judgment |
|---|---|---|
| `ApplicationProvenance` keyed by generated App `ExprId` | Source App origin, module, application span, callee span | Argument/formal owner, typed port path, original profile or licensing |
| `SourceBoundaryProvenance` keyed by `SourceBoundaryId`, when inserted | Application, callee and required argument span | `beta`, `Slots(beta)`, contribution identity or shared `xi` |
| `OriginId` passed to the callee Function subtype demand | Which source boundary motivated that demand | A Q-independent typed owner/view-kernel introduction or complete invocation relation |
| Portable explanation source role | Historical diagnostic attribution category | Independent admission or exhaustive source-contract inversion |

The source-boundary producer itself was already documented in the preceding
archaeology. This refinement isolates its timing and per-argument range shape;
it is distinct from downstream Function derivation provenance and generalized
occurrence paths, and from Specializer2's later App consumer, which reconstructs
a typed consumer from solved views.

The strongest justified historical claim is therefore local: for applications
reaching this source path, the implementation allocates a source-kind origin
and ties it to the callee's Function demand. Source coordinates are retained
only when the relevant spans are available and span recording is enabled; a
source-boundary span record additionally requires an argument range. This is
not a complete history of every application producer. Because the subtype
request may drain immediately, it establishes no pre-query registration
beyond the identity allocation and demand arguments visible in this code.

## Authority boundary and stop

The current authority remains the unresolved source-owned
`ORIGINAL_ASSOC` introduction, followed by attachment, licensing inversion,
profile/rows and independent admission. No Oracle rule, acceptance result or
representation is imported into that chain. No current theorem closes; no
production or shadow implementation authority changes. The next meaningful
step is to construct the current original source judgment from its specified
typed premises, not to infer a `beta`/slot/contribution rule from these Oracle
IDs or spans.

The frozen Oracle checkout's HEAD resolved to the stated pin; cited source
blobs matched the pinned commit. Inspected source windows: `tail.rs:89–126,
535–685`, `expr/mod.rs:193–196`, `constraints/machine/entry.rs:433–451,493–499`,
and `constraints/explain.rs:2063–2084`. No builds, tests, benchmarks, Oracle
execution, or mutations were performed. Compiler-referee review found two
minor wording issues concerning conditional span registration and prior
archaeology; both are repaired here. This remains a bounded characterization,
not a repository-wide absence claim.
