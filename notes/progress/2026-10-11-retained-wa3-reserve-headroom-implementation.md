# Retained W/A3 reserve-headroom implementation slice

Date: 2026-10-11
Status: implemented and focused-verified; the ledger arithmetic theorem and original W/A3 remain **OPEN**.
Branch: `research/simple-sub-intrusion`.

## Gate and authority

This slice addresses only the source-construction growth/rebuild headroom gap
identified in [the bounded ledger derivation](2026-10-11-retained-wa3-ledger-headroom-proof.md).
The implementation follows the approved private candidate suspension contract
§6 and does not change inference semantics, counter meanings, rollback policy,
or resource limits. The original W/A3 quantifiers and all other proof premises
remain in force.

## Implementation correspondence

`InferenceSession::preflight_bound_capacity_growth` in
`crates/yu-solver/src/lib.rs` checks history headroom before an allocation when
a one-element insertion sees `len == capacity`:

- current growth and rebuild counters each admit one more event;
- an active route journal admits one more incoming capacity-change event;
- a pre-existing row admits one more retained-growth event;
- while incoming route accounting is active, the checkpoint growth/rebuild
  counters admit the journal's existing event count plus this possible event.

All eight ordinary value/effect nested-bound reserve sites call this helper.
Each half of a direct-edge pair checks independently, after the first reserve
has been accounted. The `candidate_insert_bound_with_evidence` macro applies
the same preflight to candidate extrusion's shared nested-bound insertion
path. If capacity already exists, the helper returns without rejecting a push
because unrelated counters are exhausted. The existing post-reserve accounting
continues to charge actual capacity deltas and sample at its original sites.

The new regressions in `lib.rs` cover current counter/journal exhaustion before
reserve, an incoming failed growth on a row later dropped by rollback, the
second reserve of a direct pair, and a push using spare capacity at exhausted
counters. Test fixtures that directly set counters establish only the guard's
boundary behavior; they are not source-reachability evidence for MAX-valued
histories.

## Review and verification

Frozen code hashes reviewed:

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/lib.rs` | `31c66d1bc9cc101c6174424f5f11b7cbeb6eb497448e0a4b09b683adbacb9dd9` |
| `crates/yu-solver/src/candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |

Independent `compiler_referee` review found no blocking, major, or minor
findings in reserve ownership, counter arithmetic, and rollback/journal
coverage. Independent `spec_auditor` review found no findings against §6,
sampling invariance, spare-capacity behavior, or the test contract.

Focused checks passed:

```text
cargo test -p yu-solver bound_growth_headroom -- --test-threads=1
cargo test -p yu-solver --features shadow-apply-candidate,f5c_resource_probe bound_growth_headroom -- --test-threads=1
```

Each command ran the four matching unit tests successfully. `git diff --check`
also passed. No broad suite or benchmark was run.

## Remaining obligations

This guard repairs the pre-allocation cumulative growth/rebuild headroom
premise for the covered nested-bound reservations. It does not prove the
allocator/addressability premise needed for byte-sum representability, nor
semantic inverse totality or rollback success for every constructor-valid
retained history. Those obligations remain owned by the original W/A3 proof
and its distinct source, lifecycle, and semantic-inverse lanes. W/A3, complete
Simple-sub inference, Yulang2-derived effect hygiene, soundness/principality,
and F5 production cutover remain OPEN.
