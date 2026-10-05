# Handler release evidence at the production boundary

Date: 2026-10-06  
Status: bounded source-to-production audit; research only  
Baseline: `310a4b7bf568316daa315709c8fbf108bc343a49`  
Implementation authority: none

## Result

The approved `handler-protection-release-crossing/q1/d1` decision has a
conditional source-side crossing witness: source-realization-and-symbolic-basis
§7 records an original request at invocation, force, or handler output before
outside handling, retaining its packet and continuation. Existing production
HIR/F5 artifacts do not emit the dynamic evidence needed to connect that
observation to the approved release rule.

This is a bounded owning-path audit, not a repository-wide impossibility
claim. It does not establish that the surface language cannot express the
behavior, or that another production entrypoint cannot supply the evidence.

## Approved decision and source-side bridge

The unchanged approved answer selects release only when an independently
`'e`-attributed contribution actually crosses the marked slot after intervening
computation or handler processing. Release is tied to the same target view
while the original receiver remains active. It preserves provenance, event
identity, family/type arguments, row support, typed paths, attachment, the
original `(nu,K,D)`, and other slots' protection. It neither selects nor grants
a handler and does not consume the event or subtract row support.

At the source level, `source-realization-and-symbolic-basis.md` §7, lines
548–554, records an output observation when the original request crosses an
invocation, force, or handler output delimiter. The observation retains the
packet and suffix before later outside handling. This distinguishes an actual
output observation from the earlier dispatch-time `Observe`; it supplies a
candidate crossing point for the conditional discriminator in
[`handler release query discriminator`](2026-10-06-handler-release-query-discriminator.md).
The source-indexed callback realization retains original Force-origin
`d−/d+` occurrences, but does not associate a public `'e?` marker with that
output observation.

## Production artifacts inspected

| Artifact | What it retains | What it does not establish |
|---|---|---|
| `ResolvedExpr` in `crates/yu-hir/src/module.rs:426–449` | Lambda, integer, name and error nodes with HIR occurrence identity | An Apply/call, operation request, handler, dynamic `Receive`/`Path`, or release transition |
| `ConstraintOccurrenceId` and constraints in `crates/yu-solver/src/lib.rs:391–410` | Static source occurrence, local slot, lower/upper terms and cause | Runtime event-to-component attribution or marker-to-profile witness association |
| Lambda generation in `crates/yu-solver/src/lib.rs:1557` and four Function views in `crates/yu-types/src/lib.rs:590–620` | Structural Function endpoints and the current Bottom/Empty effect views | The concrete profile, full typed-boundary evidence or a same-target release state |
| Lexer apostrophe/question handling in `crates/yu-syntax/src/lexical/lexer.rs:760,887` | Recognition of the spelling shape | Annotation elaboration or its semantic evidence |
| `crates/yu-solver/src/tests/research_function_realization.rs:1–70` | A test-only candidate observation model; `InvocationStep::Receipt` is supplied trace data | A production-generated typed receipt or proof of production `Receive` evidence |

The available production source therefore lacks, on this path:

1. a source introduction rule deriving that dynamic event `q` belongs to the
   component binder `'e`;
2. a rule associating the marker occurrence with the intended complete
   protection/profile witness;
3. a transition/refinement connecting the source output observation to the
   approved same-target protection update before the next handler query.

The ordinary `Visible` equation still computes protection from active path and
incidence evidence. It has no released-target premise. Deleting `Path`, profile
or incidence evidence wholesale would violate the approved frame conditions;
the missing bridge must preserve them while accounting for exactly the
released protection. The test-only reconstruction cannot fill that production
gap.

## Exact next obligation and limits

Construct the component/marker/full-witness association at an existing typed
Force-output port, then prove that its source output observation refines the
approved release step for the same target view while the original receiver is
active. The proof must leave provenance and other protection witnesses intact
and must change the subsequent query eligibility at the approved time. Validate
it on a query-discriminating configuration; the same-owner false-guard example
does not suffice because its outer query is already eligible before release.

This note does not certify raw-source acceptance, all alternate HIR/runtime
entrypoints, latent transport, query refinement, soundness, principality, or
production implementation. No production code or test contract changed.

## Baseline inputs and checks

| Input | Baseline blob |
|---|---|
| Approved crossing answer | `358438b2a6d7b61408713c5dc48bb84b307c75d7` |
| Source realization and symbolic basis | `7c5fbf64af1cb46c44d612736c28907cadde3fac` |
| Source-indexed callback realization | `6f412b19dd91b4a32aa2421d2668ac2203dc6ed2` |
| Typed-boundary realization draft | `5e0499e43b3dbf04de0bcdb6c0fa5994224d8a87` |
| Typed-source owner realization | `d0c6c5e2d10cf1b72da0e8613b74641bd25b2caf` |
| HIR `module.rs` | `668d1b6f82fb17a96178a2353543d288c32e2762` |
| Solver `lib.rs` | `fa118b726ebbfdc7d32b617373b4e2cb04e84682` |
| Types `lib.rs` | `c3a4e95d199fba0784b7e6448b6bb37a1f2c7798` |
| Lexer | `39bbb4530967aa5998fa87f0e5c6031b1d9140d7` |
| Test-only Function reconstruction | `bb5041c8b283fb912f55003f7257a4f4df425130` |

All ten table entries were resolved to the listed blobs at the pinned HEAD.
Before writing, I also hash-compared the six available working files (the
approved answer, HIR module, solver library, types library, lexer and test-only
reconstruction) with their baseline blobs; they matched. The four design
documents were read from their pinned Git objects, so no worktree-equality
claim is made for those files. Reviewable scope is the listed HIR, constraint,
type-view, lexer and test-only reconstruction definitions plus the approved
answer and source-side output-observation clause. No tests, builds, executable
probes or Git operations were performed. No exhaustive search was run or
claimed.
