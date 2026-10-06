# Frozen Oracle call-boundary mechanisms: bounded novelty stop

Date: 2026-10-08
Status: frozen research-only bounded characterization; independent review pending
Yulang3 baseline: `b7687afb33b1ae3367986c6f95145eb17820de74`
Frozen Oracle: `/tmp/yulang2-oracle-rebuild`, `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Exclusive lease: this note only
Semantic/production authority: none

## Objective and result

Search CST/body dispatch, ordinary Call construction, and occurrence registration
for an overlooked historical producer of original `beta`/`Slots(beta)`, typed
path/owner/receiver incidence and complete contribution under one original
`xi=(nu,K,D)`, independently of successful solving.

**No distinct producer was found in these inspected seams.** The occurrence
and boundary route requested by this assignment is already characterized in
[presolve application types](2026-10-06-frozen-oracle-presolve-application-types.md),
[application source-boundary timing](2026-10-07-frozen-oracle-application-source-boundary-producer.md),
and [ordinary-Call novelty stop](2026-10-08-frozen-oracle-original-call-association-mechanism.md).
Upstream binding/CST dispatch and portable root export return to that same
machinery. This note records a dispatch-avoidance result, not a new original
association mechanism, proof of absence, or theorem closure.

## Governing premise and hypotheses

[Inferred Function call views](../design/2026-10-05-inferred-function-call-views.md)
§§1–5 preserve written/public/internal separation, static source identities,
typed source resolution, shared original coordinates, provisional formal/use
treatment and annotation protection. They defer exact construction judgments.
[Source contracts](../design/2026-10-05-source-contracts-and-common-allowance.md)
§§2.1–3 and 10 take the independently typed primitive/owner/view kernel as an
input; the Call inventory requires actual receiver/receipt, actual entry,
body, consumer and invocation return. C-realization assumes the supplied
kernel and typing/conformance certificates. It does not construct this input.
Approved Option 2 permits production observations without source witnesses.
No Oracle field is assigned a current semantic meaning by analogy.

The precise local hypotheses are:

1. The cited bytes match the pinned commits, as checked below.
2. The ordinary non-pipe, non-selection Name/Name application reaches the
   inspected `Expr`/application-tail dispatcher and lowers its operands.
3. For ordering beyond subtype submission, the historical subtype call returns
   normally. This is a control-flow hypothesis; it is not successful semantic
   comparison, solver soundness or completeness.
4. A source-span record requires recording enabled and the requisite ranges;
   occurrence roots require the corresponding bound/constraint records.

Established here are code dependencies and payload shapes on that bounded
route. The ordering derivation below is conditional on those hypotheses.
Treating `SourceBoundaryId`, `ExprId`, an empty occurrence path, or a root ID
as original `beta`, typed `p0`, a complete contribution or joint `xi` would be
an additional candidate assumption for which this pass supplies no bridge.
No conditional theorem about Yulang3 source semantics is claimed.

## Additional seams and local ordering derivation

All Oracle locators below are relative to the frozen checkout.

| Inspected seam | Concrete dependency | Novelty result |
| --- | --- | --- |
| `lowering/body/mod.rs:2263–2326` | Extract body CST; preallocate a definition root and enqueue SCC `RegisterDef`; configure `ExprLowerer`; dispatch body/header arguments | Definition/SCC registration precedes body lowering, but its payload is `def,root`, not a Call-owned typed slot/contribution. The caller/skeleton route is already traced in the October 6 reachable-inputs note. |
| `lowering/expr/mod.rs:267–272`, `expr/chain.rs:8–28,104–159`, `expr/tail.rs:8–17,89–126` | CST is lowered directly to computations/poly expressions; an ordinary application tail lowers the argument and invokes `make_source_app` | No intervening HIR producer appears in this specific call chain. This is already covered by ordinary-call archaeology; it is not a claim about every repository subsystem. |
| `analysis/session/occurrence_provenance.rs:70–163` | Merge existing/generalized roots, export their provenance, recover an argument location from the existing boundary table | A downstream export of the same roots and span table; no new pre-query source registration. |

Under the hypotheses, source inspection gives the strict program order

```text
lower argument (including its actual-occurrence registration)
  < allocate ApplicationArgument boundary/origin records
  < allocate result/call endpoints and negative Function demand
  < submit historical callee subtype request (may drain immediately)
  < register argument-owned ExpressionExpected roots
  < link result effects and allocate poly Expr::App
  < conditionally insert application/callee/argument spans
  < register completed expression's ExpressionActual bound roots
  < later portable provenance export
```

The key constructors are `expr/tail.rs:535–627,630–687` and
`constraints/machine/entry.rs:433–451,493–500`. Before the historical subtype
request, the boundary allocation stores only an `OriginRecord` containing
kind/boundary and a `SourceBoundaryRecord` containing origin and
`location_recorded=false` (`constraints/mod.rs:3890–3900`). It establishes a
session-local handle. It does not register a typed path, formal owner,
receiver relation, static slot inventory or complete invocation contribution.

`ExpressionExpected` is keyed by the **argument** expression and an empty path,
with the just-submitted callee/Function constraint root. `ExpressionActual`
is registered after expression lowering by copying current lower-bound record
IDs. `PendingOccurrenceProvenance` contains roots and completeness
(`constraints/mod.rs:2743–2759`); it is not the original endpoint/effect tuple
or a semantic contribution certificate. This is the existing presolve note's
characterization, repeated here only to identify the novelty stopping point.

The additional export seam also consumes these records: no roots gives an
empty sidecar (`occurrence_provenance.rs:116–118`); locations are recovered
through `source_boundary_provenance.application_argument(boundary)`
(`:125–155`). Portable conversion may omit locations on missing spans or
failed `u32` range conversion. Nothing in this export reverses the ordering
or independently types the original Call.

The historical subtype method returns `()` and may process pending work. Thus
post-submission registration should not be equated with registration conditional
on a successful Function comparison. Conversely, the absence of a success
predicate does not supply the missing independent source judgment. The current
pending `Q` and this historical request are not identified semantically.

## Independence, failures and omitted cases

Oracle code supplies historical control/data evidence independent of the
current research notation. Its lowerer, bounds, explanation export and
specializer share one implementation's assumptions. They are not independent
semantic oracles for the selected Yulang3 contract. No printed type, execution,
successful solver result, or transition-assuming checker is used here.

No executable probe, mutation, random seed or enumeration range exists for this
static method. No source counterexample is claimed. The local falsifier for
this characterization would be a cited alternate constructor before the demand
that stores and independently interprets the required complete original tuple;
the inspected additional seams did not contain one.

Failure/coverage boundaries: lowering can fail before Call construction;
missing bounds prevent actual-occurrence insertion; empty expected roots mark
provenance incomplete; disabled spans omit source-coordinate records; a
zero-argument application lacks the argument span needed by the boundary
triple. Synthetic Apps, pipe/selection/effect-operation applications and other
dispatch paths are outside this exact cut. Generalization correctness, solver
correctness, all export-budget outcomes, runtime behavior, admitted source
realizability and repository-wide absence remain unverified. The bounded
registration-symbol search included a nonexistent `crates/hir/src` operand
and returned exit 2 while still reporting infer/parser matches; that search is
not complete cross-crate evidence. One broad caller-search capture truncated;
the decisive body/dispatcher windows above were subsequently read directly.

## Checks and resources

Commands: bounded `cat`, `rg -n`, `rg --files`, `sed -n`, `nl -ba`, read-only
`git rev-parse HEAD`, and one-process Python SHA-256 plus serial `git show`
byte comparisons. Both initial HEADs equal the assigned pins. Nine cited
Oracle files and both governing designs match their pinned blobs byte-for-byte.
No tests, builds, Oracle execution, formatting, scratch output, child agents,
Git mutations or shared-record writes occurred. At most one shell/Python
process was active; Git hash checks used serial child processes. Heavyweight
process count is zero. CPU time and peak memory were not instrumented; reads
completed in subsecond tool-reported time. Assigned wall-time ceiling: 15
minutes; total wall time was not separately instrumented. No timeout occurred.

| Dependency | SHA-256 |
| --- | --- |
| Inferred-call-views design | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| Source-contracts design | `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186` |
| Oracle `lowering/body/mod.rs` | `f5e82c2109a11938cab6a5b48d8a155f6ac3029c4d26cb7f4570790e8d5f9cb1` |
| Oracle `lowering/expr/mod.rs` | `bbece8eddeba93cff358f4d14eeb9d818f4ac9170b327668457340f166e08c6b` |
| Oracle `lowering/expr/chain.rs` | `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6` |
| Oracle `lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| Oracle `analysis/session/occurrence_provenance.rs` | `90613e12e904c74d40894e6f395162c358cc632a8aecb9ddc55db542dd897268` |
| Oracle `constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| Oracle `constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| Oracle `lowering/application_provenance.rs` | `b062742b588830ce5edf1a51a9c8718aca0b81b1360b3c4c1172b09e112614aa` |
| Oracle `lowering/source_boundary_provenance.rs` | `9d9f1694d4848be9daddea986b80be833f081d1e78a31ce1a0e540b740d74412` |

Recommended next action: retire this duplicate ordinary-boundary archaeology
route and use a constructive source-rule method for the original independently
typed slot/contribution introduction. `ORIGINAL_ASSOC` remains open; no new
user decision or implementation permission is inferred.

## Commit packet

- Exact leased path: `notes/progress/2026-10-08-frozen-oracle-call-boundary-mechanisms.md`.
- Baseline SHA: `b7687afb33b1ae3367986c6f95145eb17820de74`; Oracle pin:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none introduced; inspected bytes equal the pins
  at verification. The table identifies direct source/design dependencies.
- Review status: research-only bounded novelty stop, independent review
  pending; producer self-inspection is not independent review. Writes stop
  before submission; primary owns review and integration.
- Checks already run: initial HEAD identity; lease absence; scoped novelty
  searches and direct constructor/export reduction; nine Oracle/two design
  pinned-byte comparisons; leased-artifact whitespace inspection. No tests,
  builds or Oracle execution.
- Proposed one-line research-checkpoint message:
  `research: stop duplicate Oracle call-boundary producer route`.
- Shared-record deltas intentionally left for primary/curator: optional
  dispatch-avoidance reference to this note; keep `ORIGINAL_ASSOC` and dependent
  gates open. No task/index/authority/theory/question-board changes proposed.
