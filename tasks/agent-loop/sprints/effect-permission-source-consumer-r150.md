# R150 — source laws and immutable-baseline Rust candidate

Status: proposed by the dispatcher, admitted by Luna after hash and lease review.
Objective: continue the authorized effect-permission Rust/Lean goal by deriving
the missing producer-initial-state and consumer laws, then express any
source-supported repair as a candidate patch against immutable committed blobs.
This sprint does not change the accepted source semantics or original A/B claims.

## Parent and baseline

Parent gates remain OPEN: `INITIAL-STATE`, `CONSUMER`, R149 source-to-CST,
original A/B, source/native correspondence, and production. R149 established a
conditional member-state construction and repaired R118/R119; it did not close
these gates. No source-qualified counterexample is currently established.

Baseline commit: `7a8a20bf7a92172d7732ae7b18e0955423778f02`.
Rust inputs are read only through `git show <baseline>:<path>`; no dirty working
tree Rust may be read or used. Pinned baseline hashes:

| Path | SHA-256 |
|---|---|
| `crates/yu-solver/src/candidate_source.rs` | `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49` |
| `crates/yu-solver/src/candidate_context.rs` | `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905` |
| `crates/yu-solver/src/candidate_scheme.rs` | `e2b6209e3bf486a302e52e5051be60bf7cd8187a7a1e8453087b94f77e06b814` |
| `crates/yu-solver/src/candidate_scope.rs` | `4d4ea4847ca09d53ea49ef3c411617b5a33a9e3f2d95b887842f74a12e2b7c03` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61` |
| `crates/yu-solver/src/candidate_effect.rs` | `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01` |

Governing source locators and hashes are fixed in the admission record. Read
only the original ordinary-computation, directional-protection, annotation,
and compose rules needed to derive the packet; do not infer absent rules.

## Lane A — constructive source laws (900 seconds)

Role: registered `prover`. Exact output lease:
`tasks/agent-loop/inbox/effect-permission-source-laws-r150-proof.md`.

Derive from original rules: (1) incoming input/protection state for each
producer, distinguishing intrinsic operation events, latent annotation members,
and existing Contributions; (2) same-witness transport and FreshUse conditions;
(3) consumer rules distinguishing annotation permission, actual inflow, capture,
scope release, and actual Catch processing. Do not assume arbitrary State or
seed laws. If a source rule does not determine a case, state the exact missing
premise and owner. Apply any valid result to INITIAL-STATE/CONSUMER without
narrowing source cases.

## Lane B — candidate Rust artifact (900 seconds, sequenced after Lane A)

Role: registered `implementer`. Exact output leases:
`tasks/agent-loop/inbox/effect-permission-source-consumer-r150.patch` and
`tasks/agent-loop/inbox/effect-permission-source-consumer-r150-source.md`.

After Lane A freezes, construct a patch solely against the pinned committed
blobs and the frozen source-law handoff. Candidate paths are the six Rust files
listed above. The patch is an unapplied research artifact: do not edit the Rust
working tree, apply it, compile it, or run tests. If the laws do not support a
coherent repair, return no patch and identify the exact blocker.

Preserve owner/batch/live-state identity, provider/arm identity,
permission-origin matching, rollback behavior, independent protections, and
effect-row invariants. Do not include the existing dirty `candidate_receiver.rs`
diff, whose removed checks are outside this packet. Do not read or lease the
quarantined runtime files.

## Independent review and limits

Role: fresh `compiler_referee`, 360 seconds, after both author lanes stop.
Review derivations, exact base/path hashes, patch application to immutable
blobs (without modifying the checkout), producer-to-consumer coverage, and all
preserved invariants. Adjudication and record integration: primary, 180 seconds.
Total ceiling: 2340 seconds. Rust/Lean execution, builds, tests, new cache,
scratch, environment, checkout, worktree, and nested teams: zero.

Falsifiers include an unjustified empty seed for a latent Support member,
cross-derivation deduplication, mixed FreshUse maps, lost independent protection,
or treating permission as actual inflow/capture. A candidate patch plus review
does not close the parent theorem or authorize production. Any application,
build, and focused tests require a later exact source lease and verification
packet.

## Stop and success

Success is a reviewed source-derived law that strictly reduces an exact parent
premise, plus a reviewed candidate patch if and only if the laws support one.
Otherwise freeze the precise source obstruction and keep all parent gates OPEN.
No worker may widen paths, budgets, semantics, or production authority. Writers
must stop and freeze exact hashes before review; only Luna integrates or performs
Git operations.
