# R99: unmatched outward request and its saved suffix

Status: DRAFT FOR PRE-EDIT SPEC REVIEW; no writer lease has started.
Primary: Luna `/root`.

## Fixed bounded outcome

Advance one hygiene front with a runnable finite source example: an inner
handler misses an operation, an outer handler accepts that request and resumes
it, and the resumed source suffix reaches the original inner handler. Keep the
original Simple-sub/evaluator claims, quantifiers, A/B, and adoption gates
unchanged. This is candidate source/runtime correspondence, not a general
handler or continuation theorem.

Positive fixture:

```yu
act io:
    our tick: int -> int
    our other: int -> int
my inner (thunk:[io] int) = catch thunk { io::other(p), _ -> p }
my outer (thunk:[io] int) = catch thunk { io::tick(p), k -> k 23 }
my main = outer (inner { my answer = io::tick 7; io::other answer })
```

Candidate prediction, pending preparation and the one authorized execution:
integer `23`. The initial `tick 7` crosses the inner `other`-only handler,
reaches the outer `tick` arm, and is resumed with `23`; the original suffix
then requests `other 23`, which the reinstated inner handler accepts.

Paired falsifier changes only the outer pattern `io::tick(p)` to
`io::other(p)`. Candidate prediction: an outward `UnhandledRequest` for the
declaration-owned `io::tick`, integer payload `7`, with the original suffix
retained. These outcomes are UNOBSERVED until Luna's command. Any source or
preparation mismatch, candidate conflict, wrong identity/payload/result, loss
of the suffix, dependency drift, or blocking/major review stops R99 without
repair or retry.

## Proof obligation and inputs

Bind the exact source rows to authentic LocalSource definitions/formals,
outer computation entry and operation IDs. Trace request eligibility and
ordered operation mismatch through the inner handler; trace the saved
`HandlerBoundary` through `capture_template`'s `ForwardHandler`, owner/view
remapping and `enter_template`; show where the resumed suffix emits `other`
and the current inner handler handles it. State exactly which source/native
steps are constructor facts and which are runtime observations. Reuse R88/R92
only for their reviewed, applicable premises. Runtime success does not prove
general preservation, K,D or residual projection, arbitrary Resume, A/B,
R50/R85 adoption, or production authority.

Proof outputs:

- `notes/theory/2026-10-19-r99-unmatched-outward-suffix.md`
- `tasks/agent-loop/inbox/20261019-r99-proof.md`

## Implementation and verification

Add one two-cell integration test named
`unmatched_request_preserves_original_suffix_across_outer_handling` in the
new auto-discovered target `tools/inference-playground/tests/runtime_unmatched.rs`.
Use the existing public runtime construction API and independent `CandidateInference`
preparation; add no production code and do not edit other tests.

Implementation handoff:
`tasks/agent-loop/inbox/20261019-r99-implementation.md`.

After the pre-edit spec review, frozen implementation/proof outputs and CLEAN
spec delta, Luna runs exactly once:

```sh
CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_unmatched unmatched_request_preserves_original_suffix_across_outer_handling -- --exact --nocapture
```

No retry or repair under R99. A failure is preserved as the sprint outcome.
After execution, assign a fresh independent compiler/source review; Luna
adjudicates and closes the sprint. A passing test is runtime evidence only.

## Source pins, leases, budget

Observed baseline hashes:

| Input | SHA-256 |
|---|---|
| `runtime_receiving.rs` | `6ff65fc977c88837ec279b84088a6c2d89ebfc7f78915e7ac985904fcaa26bf2` |
| `machine.rs` | `fa8dab7f7146f528ad354f336cdfe6e41a728505f9c3dd80c6df64e843dc5b46` |
| `continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` |
| `receiving.rs` | `8c81deadc48c4770f25760e9086d2053815785ff16cfd5580fa814fb83af9bd9` |
| `program.rs` | `484967c20c829344a8abe3aa583f6a65e715fb927b8d6b0ba816f0cc6291ad11` |
| `local_source.rs` | `3014628f861840ca8e716b3baf8e6a3c9dd736b1bad318b32e7a7b195ddf8786` |

The new target is not present in the baseline and Cargo auto-discovers files
under `tests/` (no explicit `[[test]]` configuration). Recheck relevant pins
before execution.

- Primary only: contract, `current.json`, review receipts and closeout.
- Implementation writer: only `runtime_unmatched.rs` and its one handoff file;
  no tests/build/CLI/Git and no production edits.
- Proof writer: only the proof note and its one handoff file; no source edits,
  tests/build/CLI/Git.
- Fresh pre-edit spec reviewer and post-freeze independent compiler/source
  reviewer: read-only, separate from both authors.
- Preserve three inherited UNKNOWN identities and quarantined paths. Admit no
  more than two production workers concurrently. Astra allocation: zero.
- Total cap 1,800 seconds: spec 180; proof 600; implementation 360; one command
  120; compiler review 240; integration/closeout 300.

R98 remains FAILED_TO_ACHIEVE as recorded; do not repair or rerun its frozen
candidate. At the next sprint boundary, rotate across the remaining hygiene
fronts and schedule a source/behavior step for method/role plus an early
user-visible runnable surface. Do not let effect storage or one hygiene front
consume all subsequent work.
