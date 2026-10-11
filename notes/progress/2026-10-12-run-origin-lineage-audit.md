# Selected `run` capture: source and contribution lineage audit

Date: 2026-10-12
Status: frozen, independently reviewed research checkpoint; bounded static source characterization
Lease: this file only; primary-assigned researcher leaf; no delegation or Git mutation
Y3 baseline: `c1041f8f4706e847bf709e36728211965be24980`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle inspected worktree: `/home/momota1029/rust/yulang2-oracle-capture`

## Objective, authority and exact premise

Find the existing owners that join the concrete source application `ev::send`
to its constraint origin, selected `run` records and actual Call output. This
is a source/artifact correspondence audit, not the constructive H proof lane.
It changes no language meaning or compiler operation.

The governing evidence is [native negative residual derivation](../theory/2026-10-12-native-negative-residual-constructor-derivation.md)
§§9–11, especially §9.2 and §11. Preserve its accepted distinction between
handled-input head acceptance and positive output survival. §11 establishes
P_sel only for the explicit `(int,int)` / `(1,42)` variant, input hash
`73b4a2d12233b9b658188f3baa17edb04c14a89f94217198befca22db4af77d9`.
The original Oracle fixture is
`notes/bugs/solved/handler_arm_tuple_payload_pattern.yu:57–64`; its final
application uses `("x",42)`. The successful variant's allocation IDs cannot be
transferred to that original input.

Semantic authority remains annotation hygiene integration §§1–5, contextual
attachment/admission §§3–6 (including §3.1), residual lineage selection
“Selected policy”, and top-level inference principles §§1–5. The latter
supersedes blanket abnormal rollback demands in the older contract. The
copied-row question is outside this packet. No pending question was consumed.

The static claim assumes completed owner calls, valid arena handles and the
inspected source bytes. It proves where correlation is produced and retained
or omitted; it does not determine runtime record membership. The current
instrumented worktree has five existing modified files, as recorded in §11;
none was edited here. No timed-out default-prelude transcript is used.

## Source-to-record map that already exists

All source locators below are relative to the Oracle worktree.

| Step | Exact owner | Retained identity / limitation |
| --- | --- | --- |
| CST application | `crates/infer/src/lowering/expr/tail.rs:88–124`, `apply_arguments` | Lowers each actual argument, retains callee/application/argument byte ranges, then calls `make_source_app`. |
| Source origin allocation | `tail.rs:630–688`, `make_source_app`; `constraints/machine/entry.rs:431–452` | Allocates one `SourceBoundaryId` and `OriginId` of kind `ApplicationArgument`; supplies that origin to the Call demand. Stores boundary-keyed source spans and ExprId-keyed application ownership. |
| Span table | `lowering/source_boundary_provenance.rs:10–48`; `lowering/application_provenance.rs:13–62` | The former retains application, callee and argument spans. The latter retains application ExprId, module and spans, but no OriginId, boundary, constraint ID or computation effect slot. These are distinct tables. |
| Four-port demand | `tail.rs:535–586`, `make_app_with_origins` | Allocates result Value, result Effect and call Effect; emits `Var(callee.value) <: Fun(arg.value,arg.effect,return_effect.upper,result_value)` with the source origin. Looks up its canonical `ConstraintRecordId` and registers it under `ExpressionExpected` of `arg.expr`. |
| Constraint retention | `constraints/mod.rs:3876–3899`; `constraints/machine/entry.rs:1357–1420` | Canonical records keep additive `root_origins`, structural, replay, row and scheme-instantiation derivations. Duplicate semantic admission adds the new origin; it does not overwrite it. OriginRecord retains kind and source-boundary ID; source spans live in the separate session table. |
| Bound / proof retention | `constraints/mod.rs:762–788,3225–3246,3316–3355` | BoundRecord keeps owner, endpoint, weights and derivations. Derivations and selected proof carriers name actual constraint/bound/origin parents. IDs identify session records, not source contributions by themselves. |
| Structural Call consumer | `constraints/machine/propagate.rs:210–266` | Derived edges retain the parent constraint and distinguish FunctionArgument, FunctionArgumentEffect, FunctionReturnEffect and FunctionReturn. Argument Effect uses swapped context; the pure passthrough branch is explicitly marked. |
| Source explanation | `constraints/explain.rs:221–318,600–613`; `analysis/session/occurrence_provenance.rs:120–151` | Existing explanation/export traverses retained derivations and resolves source boundaries to argument spans. Budget/completeness must be inspected; raw ancestry and selected claim-qualified proof are different observations. |

Consequently, a successful application-boundary observation can join the
concrete send source span to its actual OriginId and demand ConstraintRecordId.
Selected bound ancestry can then be queried through existing retained records.
The §11 trace instead reports selected entries and proof carriers, without this
source-boundary map or a complete parent closure. The producer of record 256 is
163, and record 258 has result 164 and premises 255/257; that is the beginning
of an ancestry query, not its source-qualified conclusion. This audit assigns
no new numeric origin or constraint ID to either concrete application.

## First missing correlations and downstream omissions

The first missing **explicit application-to-result-Effect ownership map** is at
`make_app_with_origins` / `make_source_app` itself. `tail.rs:614–624` emits
callee-evaluation Effect to result Effect and return-effect lower to result
Effect using `OriginId::internal()`. These records retain their endpoints, but
there is no structural parent link from those admissions to the source Call
demand in this owner. The application ExprId is created at 626; the returned
`Computation` contains result slots, but the application provenance insertion
at 654–663 stores spans only.

This is a metadata omission, not evidence of absent effect propagation.
`crates/infer/src/typing.rs:1–5,18–24` explicitly makes expression computation
slots ephemeral. `lowering/expr/chain.rs:17–26` registers ExpressionActual
roots for `computation.value` only. `tail.rs:577–585` registers the Call demand
against the argument's expected Value occurrence. Neither registration stores
the application's result Effect. A graph inverse search might discover
candidate edges, but this packet has not proved a unique source/output join
from that inverse search and does not recommend guessing by ID adjacency.

A separate, later omission is explicit in
`crates/infer/src/generalize/provenance.rs:318–337`: when collecting a root
positive Function, the witness collector always visits its Value argument but
visits argument Effect, return Effect and return Value only when
`path.depth() != 0`. It therefore does not create a root
FunctionReturnEffect witness for the selected `run` Function through this
branch. The source comment confirms that changing those root witnesses would
change existing bounded-query topology. This does not erase the Function
ports, compact query result, final scheme or raw solver records.

`analysis/session/instantiate.rs:56–83` captures generalized witnesses before
finalization, records them, then installs the actual finalized scheme.
`generalize/provenance.rs:23–79` checks structural paths against the generalized
compact root and exposes incompleteness instead of a whole-definition fallback.
`analysis/session/instantiate.rs:345–525` consumes the actual target scheme
and projects retained witnesses into instantiation derivations and routes.
These owners provide a real continuation for retained witnesses; they cannot
silently create the root Effect witness omitted by the collector.

Thus the finalized §11 row tail and return Effect both being `'9` establishes
a scheme coordinate relationship. It does not attribute a particular concrete
send contribution to that coordinate. Likewise, finding a send OriginId among
selected-root explanation ancestors would establish derivation ancestry, not
that this origin's concrete effect is retained in the final Call output.

## Smallest discriminating observation seam

Recommended next action: authorize one bounded, observation-only capture of the
same byte-identical int variant at the following existing owners, with one
verification owner. This packet does not implement or execute it.

1. While `make_app_with_origins` locals coexist, retain/emit source boundary and
   OriginId, callee/argument/application ExprIds, all callee and argument Value
   and Effect coordinates, result Value/Effect, call Effect, demand endpoint
   handles and its canonical ConstraintRecordId. Retain the actual
   `return_effect.upper/lower` handles, not a guessed bare slot. Emit the two
   forwarding constraint IDs with their exact endpoints/weights. Complete the
   event with `make_source_app`'s source spans. This supplies the association
   currently lost after the returned Computation is consumed.
2. At the accepted §11 root/epoch, export both the selected proof support and
   bounded ancestry closure for 256/258 (including 163/164/255/257). Resolve
   source Origin leaves through the existing boundary span table. Inspect every
   incompleteness/truncation flag; do not use the cfg(test) debug walker as an
   implicit authorization to edit test or compiler code.
3. At actual `run` use instantiation and final outer application, observe the
   target/use IDs, actual Function ports and forwarding/output Effect records.
   Query the designated result Effect with explicit status and parent support.
   Raw records can be observed directly for this research seam; adding root
   Effect witnesses to production generalization is a separate scope decision.

This distinguishes source ancestry, reached input-head acceptance, scheme
port mapping, and actual output observation. It may find no source ancestry
in selected definition records and still find the actual instantiated Call
route; neither outcome can be decided statically here. A complete positive
trace is operational correspondence evidence, not H or complete Call proof.
Failure conditions include a mismatched input, missing application-boundary
event, missing designated result Effect, unsuccessful query, scope fallback,
incomplete ancestry or event-limit truncation. Matching family spelling,
endpoint shape or allocation order is insufficient.

## Checks, coverage and dependency snapshot

Checks run: bounded `rg`, `sed`/`cat` source reads; read-only HEAD/status checks;
SHA-256 dependency snapshots. No builds, tests, Oracle execution, probes,
mutations, random seeds or enumerated input ranges. One worker, sequential
lightweight shell reads, zero heavyweight processes. Wall time stayed within
the 30-minute packet; exact CPU time and peak RSS were not measured.

The source audit is grounded in the actual Oracle constructors/consumers and
the reviewed §11 capture; it is not an independently implemented semantic
oracle. It shares that capture's instrumented baseline and input premise.
Some initial wide search output was truncated and two guessed source paths
were absent; all decisive owners listed above were subsequently read directly.
No claim relies on complete
repository-wide search or missing logs.

Independent review: compiler-referee found no blocking, major or minor issue.
The review confirmed the bounded application-to-result-Effect omission,
root-Function Effect witness omission, and the proposed observation seam. It
did not establish concrete runtime IDs, output membership or any inference
theorem.

Direct snapshots (SHA-256):

| Dependency | Hash |
| --- | --- |
| Y3 `notes/theory/2026-10-12-native-negative-residual-constructor-derivation.md` | `d4dff22c2d5f171d8236e9a7e8a9e144ee3e12dc9a1e8642cc9f89f8740eb2d3` |
| Oracle `crates/infer/src/typing.rs` | `b6ade453931d288c03332770fa76022abf90f1276466faeefa3d647be63bcef6` |
| Oracle `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| Oracle `crates/infer/src/lowering/expr/chain.rs` | `e7b4c12f4abb58ad8b9c57045e61aa2aa94ba549bc0442b814417a33c16d47f6` |
| Oracle `crates/infer/src/constraints/mod.rs` | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| Oracle `crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| Oracle `crates/infer/src/constraints/machine/propagate.rs` | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| Oracle `crates/infer/src/generalize/provenance.rs` | `83859368c64d27abb5896f1efc491b7fd616adf893b03d36d99b8f57da1792e0` |
| Oracle `crates/infer/src/analysis/session/instantiate.rs` | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| Oracle instrumented `crates/infer/src/analysis/session/generalize.rs` | `4ea4821eb197ceecb82db9c8520458ea1b14f40f2d1e8e7b0c79566279e3e988` |
| Oracle instrumented `crates/infer/src/compact/collect/mod.rs` | `23dce0d501aac161b0bd4d702ba6eda65c45a38f23c53965b62b32537a084b7a` |

Unverified: concrete numeric origin/demand/output IDs, selected-record source
ancestry, root Effect witness completeness, post-instantiation output
membership, original str fixture, observational equivalence of instrumentation,
arbitrary source programs, H, complete Call, soundness and principality.

## Commit packet

- Exact leased/changed path: `notes/progress/2026-10-12-run-origin-lineage-audit.md`.
- Y3 baseline: `c1041f8f4706e847bf709e36728211965be24980`; Oracle baseline:
  `a58eefc31e22141574b6f20c6a5748151c6d79f1` plus the pinned §11 instrumentation.
- Dependency changes made by this worker: none. Existing instrumentation hashes
  match §11; direct dependency snapshot appears above.
- Claim/review status: frozen, independently reviewed bounded source characterization;
  source-to-output contribution gate remains OPEN. Primary owns review and Git.
- Checks already run: static owner reads, HEAD/status and dependency hashes;
  no builds/tests/probes. No production or shared-record edits.
- Proposed commit message: `research: locate run source and output lineage observation seams`.
- Shared-record deltas intentionally left for primary/curator: link this note
  from the current source-contribution gate; record the missing application
  result-Effect association and root FunctionReturnEffect witness omission;
  assign the bounded actual output capture. Preserve §11 P_sel, original
  semantics and all parent proof/cutover gate statuses.
