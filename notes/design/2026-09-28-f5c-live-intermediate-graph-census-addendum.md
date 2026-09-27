# F5c live intermediate graph census

Status: Authoritative; scoped implementation complete under the user's delegation to choose and proceed (2026-09-28)
Scope: define the live intermediate graph size dimension required by F5c §5 during normalization
Related authority: `2026-09-25-f5c-flat-indexed-stack-independent-draft.md` §§5, 7; F5 §§26, 34
Decision: per invocation, count the checked sum of live Normalizer node entries and stored child-ID slots; use actual lengths, not capacities
Approved-by: user (delegated formula choice and authorized proceeding on 2026-09-28)
Reviewed-by: `compiler_referee` and `spec_auditor` (2026-09-28)
Implementation-reviewed-by: `spec_auditor` and `performance_auditor`; the repaired batch witness passed a fresh `spec_auditor` delta review (2026-09-28)
Supersedes: none; narrows only the previously unspecified live-intermediate-graph census formula

## 1. User direction and boundary

On 2026-09-28, the user removed the overall work-effort ceiling and delegated
the remaining census choice to the primary agent. The user authorized both
pending continuations to proceed. After clean independent compiler-referee and
specification review, the primary selected the formula in §2 under that
delegation. This addendum does not select a compiler numeric ceiling, an
overall work-meter limit, a production cutover, or F5c acceptance.

The base F5c proposal already requires separate pre-growth admission for live
intermediate graph size. It does not define how to count that dimension. This
addendum defines only that count so the existing gate can be implemented.

## 2. Census formula and lifetime

Within one F5c normalization invocation, the logical intermediate graph size
is the checked sum of its live Normalizer node entries and stored child-ID
slots:

```text
Normalizer.nodes.len() + Normalizer.children.len()
```

The current normalization entrypoints create one `Normalizer` per invocation.
The batch candidate uses that same `Normalizer` for positive and negative
nodes and children across all staged members. Do not reset the census at a
member boundary. Separate normalization invocations, including concurrent
independent solver invocations, keep separate census lifetimes; this is a
logical per-invocation admission, not a process-wide memory ceiling. Keep
counting child-ID slots that remain stored after a normalization pass makes
their parent entries unreachable or deduplicates members; they remain live
until the owning buffers are truncated or dropped.

If a future single normalization invocation keeps more than one intermediate
Normalizer graph live at once, it must aggregate all of those owners under one
shared admission state before any graph lane grows. Per-instance checks alone
would not satisfy this rule. The present single-owner source path needs no
second-owner runtime witness; source review and multi-member accumulation
coverage must confirm the owner boundary.

Before reserving or appending a node or child slot, use checked arithmetic to
compute the post-append combined count. The projection includes every node and
child slot that the operation will add, even when it grows the child lane before
the node lane. Arithmetic overflow returns the existing
`SolveAvailabilityError::IdentityExhausted` before that operation changes a
Normalizer lane. The gate does not add a numeric limit; the separate resource
subgate must select and approve any supported boundary.

The formula counts logical lengths. It does not count `Vec` capacity, source
`FlatDraft` arrays, emitted output `FlatDraft` arrays, logical parent-child
incidences, descriptor words, roots, bounds, or repeat work. Their existing
admissions and the F5 §§26/34 physical-capacity ledger remain separate. In
particular, rebuilt output may coexist with the Normalizer graph until drop;
the same-time physical ledger continues to count both owners.

## 3. Implementation and evidence

Implement the projection in `f5c_normalization.rs` before the first growth of
either Normalizer graph lane, for both boxed and flat candidate construction.
The shared `push_node` path must check child slots plus the node before it
reserves the child lane. The boxed `take_values_into_children` path must include
its later node in the check before reserving child slots. `push_node_at` must
check node growth before reserving the node lane. Keep the census derived from
current lengths rather than a separately cached count; failure drops or rolls
back the existing owner and cannot leave a stale counter.

Focused evidence must cover checked arithmetic boundaries, both Function
child slots, cumulative shared accumulation across multiple staged members,
rejection before graph-lane growth, and error cleanup when a later lane reserve
fails after an earlier graph lane grew. Source review must confirm one owner
per current normalization invocation and identify every path that grows its
node or child lane. Preserve normalized values, descriptor and public-counter
order, and boxed/flat parity. Do not add a source traversal, per-child
allocation, or numeric threshold to implement this census.

The implementation checks the projected combined length before `push_node`
reserves child slots, before boxed `take_values_into_children` grows its child
lane, and before `push_node_at` reserves a node. The actual two-member
`normalize_flat_batch_metered` test observes a batch size greater than each
single-member size and equal to their sum. The observation is `cfg(test)` only.
Focused evidence also covers arithmetic overflow, both Function child slots,
rejection before lane growth, and dropping/retrying after a later node reserve
fails following child growth.

Selected M2 for implementation because the gate spans boxed and flat growth
paths and puts checked arithmetic on a construction path. The performance
review found constant checked work per appended graph entry and no new scan,
allocation, clone, or timing concern. The first specification review found the
multi-member accumulation evidence incomplete; a fresh delta review closed
that finding against the real batch path.

Checks passed: the `f5c_normalization::tests::` filter (29), the actual
two-member batch witness (1), `RUSTC_WRAPPER= cargo check -p yu-solver --tests
--offline -j 2`, `cargo fmt --all -- --check`, and `git diff --check`. The
default sccache wrapper initially failed with a local EPERM; the same focused
test commands passed with `RUSTC_WRAPPER=`. No full package suite, benchmark,
or resource probe ran; measurement budget consumed: zero. Numeric boundary,
production cutover, F5e, and overall F5c acceptance remain separate open gates.
