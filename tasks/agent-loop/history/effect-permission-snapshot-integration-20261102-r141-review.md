# R141 fresh independent static integration review

Verdict: **CHANGE REQUEST — one BLOCKING finding.** The frozen patch has an
integration visibility defect and does not satisfy the contract's acceptance
gate. No additional major or minor correctness finding was identified in this
bounded static review. Parent inference soundness, effect-hygiene H, A/B and
production remain OPEN.

Reviewer: `/root/r141_review`; session
`EFFECT-PERMISSION-SNAPSHOT-INTEGRATION/20261102-R141`. Independent of the
producer. No delegation. The review inspected the actual patch and immutable
source; producer explanations and the previous review verdict were not used
as evidence of correctness.

## BLOCKING B1 — private return types cross the sibling-module test boundary

Locations in the proposed `crates/yu-solver/src/candidate_effect.rs`:

- 3742–3744: the existing `tests` module calls `one_successful_call(...).expect(...)`
  and binds its returned Snapshot.
- 5250–5251: `SnapshotError` has private visibility.
- 5302–5307: `Snapshot` has private visibility.
- 5501–5503: `pub(super) fn one_successful_call` exposes
  `Result<Snapshot, SnapshotError>` to its parent and the sibling test module.

These are handoff lines 45–47, 76–77, 128–133 and 327–329 respectively.
The baseline `tests` module starts at 2563; the new comparator is a sibling
module starting at proposed 5231, not the lexical parent of that test.

Concrete failure: with the test configuration enabled, the call expression
uses types private to `r140_ordered_snapshot_candidate` from outside that
module's privacy scope. Rust type inference and `Result::expect` do not grant
access to a private return type. Raising the function alone to `pub(super)`
does not make either type accessible. The fixture therefore cannot compile
as proposed; compiler execution was expressly excluded, so this finding is
static language/privacy analysis, not an observed compiler diagnostic.

Violated gate: R141 requires a complete integration patch accepted without a
correctness issue, and explicitly assigns visibility/type fit to this review.
The handoff's visibility rationale at line 27 incorrectly treats inferred
consumption as sufficient.

Minimum repair: give both returned types visibility covering `candidate_effect`
and its test descendants, for example `pub(super) struct Snapshot` and
`pub(super) enum SnapshotError`, while retaining private fields; or expose a
wrapper whose complete result type is accessible and perform private Snapshot
consumption inside the comparator module. Freeze the corrected complete patch
and new byte/hash evidence, then review the changed integration seam. A future
authorized compilation can confirm this repair; no compilation is authorized
by this packet. Changing only the caller's binding or omitting a type annotation
does not repair the owning API boundary.

## Independently checked evidence

Baseline commit: `a88e405b1b1c1b99a6c38e6180c977454b2507e6`.
All patch matching and reconstruction occurred in memory only. Each hunk's old
lines and declared old/new line counts were checked exactly against the
immutable blob; no source file, scratch source or worktree patch was created.

| Input/output bytes | Bytes | SHA-256 |
| --- | ---: | --- |
| R141 contract | 3734 | `7d74760aaa32e97bcced1c6574871ca5e2b4d8fd975c4db44e04bd2f05e56d40` |
| R141 admission | 994 | `43f7b3320df839134db3377d63536fd4edfc305b4a2827949e9a16502763c4b9` |
| Frozen R141 source handoff | 25181 | `65c3d181b50c45f1716092e94a519aaa74a40f93a863bf1f264d1f1da12be76f` |
| Immutable baseline candidate_effect.rs | 301873 | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| Exact extracted unified patch, final newline included | 17447 | `b43f617bba377d80ffe83f187b1dfe073b7f1f30765d0ba8a1efc8a9d152ff5a` |
| In-memory target | 318098 | `c476a352bda63d3401913e7142928e005b3602ac252bf8faf175443cd579140b` |
| Frozen R140 source | 28566 | `3335922fa8b259a1f4dea95bbf72e4ee6db8a99d7dd22fce25b3909e91aa8f56` |
| Frozen R140 review | 11552 | `d3a66d051dacb2cca835325adaf081865e08987fe253aed56d89f30f2c531624` |
| Immutable solver lib.rs | 1662249 | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| Immutable HIR source_annotation.rs | 35724 | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |

The frozen handoff hash was rechecked immediately before writing this receipt.
The cited target locations refer to the in-memory proposed result, not any
working-tree source.

## Semantic and integration checks

This artifact adds an observation/comparison boundary to a regression. It
does not repair a production compiler cause or claim to implement permission
consumption. Its ownership is appropriately confined to test evidence, apart
from B1 at that new helper boundary.

- The complete diff changes only the selected first successful fixture call
  and appends the comparator module. Existing path-order assertions, complete
  metadata checks, distinct row/equal family assertions, ordered row/member
  pairing, duplicate refusal and both failure-injection rollback checks are
  unchanged. Neighboring capture tests are unchanged. The fixture retains one
  selected successful constructor invocation; its intentionally failing
  duplicate invocation and two failing-session invocations remain present.
- The helper computes expected rows before mutation, captures the same
  session State's permission count, invokes the native constructor once in
  `with_route_transaction`, then reacquires that same session State and reads
  precisely `get(before..)`. Immutable native construction at 1897–1976
  appends local permissions only after links 43/44; subsequent fallible
  sampling remains inside that constructor's success boundary.
- Immutable `lib.rs:9546–9605` confirms transaction ownership: constructor
  errors reach rollback, while successful operations commit. Post-success
  encoding/comparison errors return no Snapshot and do not promise rollback
  of the committed constructor. That is consistent with this research scope
  and the top-level inference principles; a new general restoration rule is
  neither needed nor implied.
- Native `candidate_effect.rs:1601–1748` independently matches the source
  projection: negative root, polarity reversal on Function arguments,
  unchanged result polarity, argument subtree/result subtree before the two
  immediate ports, indexed tuple traversal and the same tuple rejection.
  Emission retains precisely negative, nonempty concrete, zero-symbol rows.
  The AAR and RRR source paths therefore remain distinct and ordered.
- One shared full-Eq tagged table encodes expected and native rows; native
  interning of an unexpected identity cannot alias an existing different
  identity. Parameter, owner/index position, occurrence, owner, scope, exact
  path, source row and concrete sequence are compared in order, including
  multiplicity and length. HIR `SourceEffectId` includes module/declaration
  identity; the comparator does not substitute display names for it.
- Root-entry images remain separate and are checked before/after rather than
  concatenated with nested permissions. The chosen fixture's entry inventory
  is empty, so this is not evidence for nonempty root-entry construction.
  Root annotation rows remain outside the nested traversal.
- Returned errors expose no partial Snapshot. Explicit reserve/width failures
  are handled; infallible cloning/allocation aborts are not claimed to be
  recoverable errors. The new code creates no production publication path.

Governing sources read: `rules/design-authority.md`; Authoritative
`2026-10-11-yulang-inference-top-level-principles.md`;
`2026-10-10-annotation-effect-hygiene-integration.md` §§1–1.2; and
`2026-10-18-npair-source-admission-adoption.md`. The latter requires the normal
source route for admission evidence. This artifact explicitly limits itself
to an internal producer fixture and does not purport to discharge that gate.

## Limits and STOPPED receipt

No working-tree `candidate_effect.rs`, its diff, or other quarantined/dirty
source was inspected. No source edit, filesystem patch application, Cargo,
build, test, Lean/Lake, toolchain/environment creation, Git index/ref mutation,
or descendant worker occurred. The initial `python` command was unavailable;
the same in-memory byte inspection ran with `python3`. This is not a Rust test
or compilation receipt.

Accepted-source uniqueness, SourceNodeKey injectivity, index-to-HirParameterId
correspondence, all-source/native order, the unchecked Lean candidate,
consumer/execution behavior and all parent theorems remain unestablished.
The sole write is this leased review receipt. Worker state:
**STOPPED_WRITING / STOPPED**, no descendants and no outstanding scratch.
