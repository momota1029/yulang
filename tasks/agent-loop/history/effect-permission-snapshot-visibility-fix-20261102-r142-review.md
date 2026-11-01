# R142 fresh independent static visibility review

Verdict: **PASS for the bounded patch-only visibility correction.** R141 B1 is
closed in the corrected candidate. No BLOCKING, major, or minor compiler
correctness finding was identified. This is neither compilation evidence nor
source integration approval. Parent inference soundness, effect-hygiene H,
A/B, accepted-source correspondence and production remain OPEN.

Reviewer: `/root/r142_review`, session `R142-INDEPENDENT-REVIEW`; fresh and
independent of both R141 author and reviewer. No descendants. Requested role:
compiler referee, `gpt-6.1-sol/medium`; effective model/effort UNKNOWN in this
worker context. Sole write lease: this receipt. The actual patch and immutable
baseline, rather than the producer's explanation, establish the conclusions.

## Cause and visibility boundary

The correction repairs the owning helper API boundary. In the in-memory
proposed `crates/yu-solver/src/candidate_effect.rs`, `tests` begins at 2563 and
`r140_ordered_snapshot_candidate` begins at 5231; they are siblings. The call
at 3742–3744 needs access to both types returned by the helper at 5501–5503.
`pub(super) enum SnapshotError` at 5250 and `pub(super) struct Snapshot` at
5302 now make both types visible throughout their parent `candidate_effect`
and its descendants, including the fixture. The error derives Debug, meeting
`Result::expect`'s error bound. Snapshot needs no Debug bound for this operation.
No annotation or field access is required to bind the inferred result or drop
it. The function itself retains its existing `pub(super)` visibility.

Snapshot's fields at 5303–5306 remain private. Its private component types
therefore do not create an inaccessible public signature. The two declarations
are the only target-byte differences from R141 v1, each adding `pub(super) `.
No caller-side workaround, consumer relaxation or new production interface is
introduced. Both caller and comparator remain under cfg(test), and the parent
module remains under the existing shadow-apply-candidate feature gate.

Precision about the handoff prose: its statement that SnapshotError variants
remain private is inaccurate in Rust. Enum variants and their payload fields
inherit the enum's visibility. They are therefore visible at pub(super) scope;
Snapshot's struct fields remain private. The admitted repair explicitly chooses
pub(super) for the error enum, whose payload is only an index and static field
name. This does not expose private solver state or defeat the intended opaque
Snapshot boundary, so it is not a compiler correctness finding.

## Full patch and invariant checks

The entire corrected patch was read and reconstructed against the pinned
immutable blob in memory. Each old hunk line matched exactly, both old/new line
counts matched, and both new start positions matched. The patch changes the
selected successful fixture call and appends the comparator module; target
comparison with R141 proves no other implementation or fixture change.

- The helper invokes candidate_formal_annotation exactly once, inside
  with_route_transaction (5517–5518), then reacquires the same session State
  and samples precisely get(before..) (5514, 5520–5525). The fixture's duplicate
  refusal and both failure-injection transactions remain untouched.
- Native baseline constructor 1897–1976 publishes retained permissions after
  links 43/44 and returns through the existing transaction owner. Immutable
  lib.rs 9546–9605 confirms commit on successful constructor return and rollback
  on constructor error. Later comparison failure publishes no Snapshot; it
  does not promise rollback of an already committed successful constructor.
- Native baseline traversal 1601–1748 matches the comparator's negative root,
  Function argument polarity reversal, result polarity preservation, child
  subtree order before immediate ports, and indexed Tuple traversal/rejection.
  Emission keeps negative nonempty concrete rows with no symbolic variables.
- One full-Eq tagged table is shared by expected and native images. New native
  identities cannot alias a different existing key. The comparison checks
  parameter, owner/index position, occurrence, owner, scope, exact path, source
  row and concrete sequence, including multiplicity and row length/order.
  Immutable HIR SourceEffectId carries module and declaration identity, rather
  than relying on spelling. Root entries remain a separate before/after image.
- Existing fixture assertions for AAR/RRR order, full metadata, distinct rows
  with equal concrete families, native paired row projections, duplicate
  rejection and rollback are byte-preserved. Neighboring tests are untouched.
  The empty root-entry inventory and selected fixture do not establish sibling
  source cases or nonempty root-entry construction.

Governing sources inspected: root AGENTS.md and AGENTS.pre-sprint.md;
current.json and agent-loop README; R142 contract/admission; R141 contract,
frozen handoff and frozen review; rules/design-authority.md; Authoritative
2026-10-11 top-level inference principles; annotation-effect-hygiene integration
§§1–1.2; and 2026-10-18 NPAIR source-admission adoption. The normal source route
is required for accepted-source evidence; the unchanged internal-producer
fixture does not supply that evidence. AST/CST, source admission, consumers and
production semantics are unchanged by these two visibility modifiers.

## Independently verified bytes

Baseline commit: `a88e405b1b1c1b99a6c38e6180c977454b2507e6`.
Patch hashes include the exact extracted diff's final newline.

| Input/output | Bytes | SHA-256 |
| --- | ---: | --- |
| R142 contract | 3268 | `41f0f3383dedb7812affa1ec4c2b36cae6c339071773fd12a5ef00e5f8c17cc7` |
| R142 admission | 712 | `c0857063b04029af0d9f82f5ee45660c8de1d4df61efbf936e2dd36c4d0bcc17` |
| Frozen R141 review | 8817 | `be08b8fa589aa0d2a91bd0468b92620e141093873e094c3412854d4de717f650` |
| Frozen R141 handoff v1 | 25181 | `65c3d181b50c45f1716092e94a519aaa74a40f93a863bf1f264d1f1da12be76f` |
| Frozen R142 handoff v1 | 22153 | `78ee6098377e95ac9b906a6eb582ac668827a7a834d0368e78528da45f14d417` |
| Immutable candidate_effect.rs | 301873 | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |
| R141 extracted complete patch | 17447 | `b43f617bba377d80ffe83f187b1dfe073b7f1f30765d0ba8a1efc8a9d152ff5a` |
| R141 in-memory target | 318098 | `c476a352bda63d3401913e7142928e005b3602ac252bf8faf175443cd579140b` |
| R142 extracted complete patch | 17469 | `0cbeb277433288d3cb6e56469bf453f57bdf36c31ef2219180c1142304211484` |
| R142 in-memory target | 318120 | `8fb4c52b89069f4ffcf203c50204869fed91d1fb5b3fa7738d10592b1cb072ce` |
| Immutable solver lib.rs | 1662249 | `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be` |
| Immutable HIR module/source_annotation.rs | 35724 | `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f` |

The frozen R142 handoff hash was rechecked immediately before this receipt.
The exact two-line delta is independently computed from the reconstructed
R141 and R142 targets, rather than accepted from the producer's claim.

## Limits and cessation

No dirty/quarantined Rust source or source diff was read. No candidate was
materialized, no filesystem patch application occurred, and no build, Cargo,
test, Lean/Lake, environment creation, scratch source or Git mutation occurred.
An initial immutable HIR lookup used a nonexistent shadow/source_annotation.rs
path and failed; git ls-tree located module/source_annotation.rs, which was
then inspected. All successful source reads used git show at the pinned commit.

The verdict is bounded static language/type/privacy analysis, not observed
Rust diagnostics or runtime confirmation. General accepted-source uniqueness,
SourceNodeKey injectivity, parameter correspondence, source/native equality,
Lean validity, consumer execution and parent theorem closure are unestablished.
No elapsed wall-clock value was authenticated; assigned review limit: 240 s.
The sole output is this receipt. **STOPPED_WRITING / STOPPED**; no descendants,
outstanding writes or scratch artifacts.
