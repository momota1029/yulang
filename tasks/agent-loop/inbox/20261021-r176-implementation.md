# R176 implementation handoff — Luna lane, revision 1

Contract: `admission-to-consumption-20261021-r176`, revision 1, SHA-256
`b7ab83dc1d2e67b9d525f7e6ee42d34fd3a2bb649423697399758f7b886b0a7c`.

Status: **NO_SAFE_CODE_SLICE; writes STOPPED**. No solver source path changed
in R176. This is a construction-order/resource analysis, not implementation or
proof certification.

## Frozen source and constructor order

All reads used `/tmp/r176-inputs/v6-plus-admission-owner/`, seven immutable
owners. Relevant hashes: `candidate_effect.rs` `c1d7ce19…`; `candidate_extrusion.rs`
`7c9a46d3…`; `candidate_context.rs` `a08ff106…`; `candidate_scheme.rs`
`48094aff…`; `shadow_apply.rs` `2b0e46f2…`; `lib.rs` `24f48035…`; HIR
`module.rs` `153a23ec…`. Baseline counterparts are frozen in the contract.

The newly pinned native admission path is more complete than R175 could see:

1. `candidate_scheme.rs::begin_candidate_fresh_bound` takes the selected
   captured bound, computes mapped owner/item endpoints and relation, and passes
   its imported antecedent, use origin, source bound and mapped relation as
   `BoundAdmissionCause::FreshUse` to restoration.
2. `candidate_extrusion.rs::candidate_insert_bound_with_evidence` calls
   `candidate_bound_origin_with_evidence` before physical insertion. It then
   reserves emission evidence, appends to the selected physical row lane,
   reads back the exact slot and BoundKey, optionally registers the capture
   incidence, and emits evidence linking the admission ID to the physical
   slot/readback.
3. `candidate_effect.rs::candidate_bound_origin_with_evidence` stores the
   actual cause. In scoped mode FreshUse calls
   `candidate_context_reuse_fresh_relation`, which checks the imported snapshot
   source bound/relation, mapped pair and exact `Dependency::Transport` with
   `use_origin` and FreshUse witness. The resulting relation/cause are passed
   into `context.evidence_admit` for both duplicate and new origin entries.
4. `candidate_effect.rs::candidate_register_capture_bound` records a tail/source/view
   incidence only for the recognized negative effect-row-to-Allowance shape.
   It has no retained pointer to the later consumer identity. Apply construction
   remains later in `shadow_apply.rs::admit_candidate_fact`; the existing query
   still requires the later relation in an earlier provider Capture. No
   source-authenticated same-provider bridge from this admission to both
   ordered Replay parents and consumed/reused FunctionPorts follows from the
   constructor chain alone.

This establishes a faithful local **constructor-order account** for the pinned
case. The independent proof lane decides what formal premises the operations
support. It does not justify deleting the failed membership predicate or
joining by endpoint alone.

## Resource and recovery analysis

Admission mutates/records evidence and samples incoming-route resources before
physical insertion. Restoration then reserves, appends and reads the physical
bound; capture registration may allocate and sample resources before the final
emission record. Several returned errors can therefore occur after earlier
state changes; the existing route journal/checkpoint owns recovery. This order
must be preserved by any correction.

R174-v6 adds inline receipts to core records and a completion vector. The
current tally subtracts `size_of::<Option<SourceDrainReceipt>>()` from larger
layouts, which does not demonstrate matching allocation requests or baseline
capacity decisions. `try_reserve` on optional evidence can consume shared
allocator capacity needed by a later inference allocation, even when its own
failure is ignored. Rollback truncates the completion vector but retains its
capacity. The Arc-backed `HirOccurrenceId` clone avoids deep-copying identity
payload, but refcount headroom, shared allocator behavior and unwind/publication
remain open. No arithmetic-only code patch resolves these obligations.

**No safe code slice** follows while the source-to-Apply consumer association
and resource behavior remain unproved. Preserve R174-v6 as NOT_CLEAN and
unintegrated. All parent, A/B, source/native and production gates remain OPEN.
Probe remains `NOT_RUN`.

## Frozen candidate manifest for proof application

Luna stopped all source-code write lanes. These candidate bytes match the R174-v6
snapshot; R176 made no code delta:

```text
24f480355979ee5d96305a08abf6aab67025ede32c2a1575b779e46f5e23b436  crates/yu-solver/src/lib.rs
a08ff10637f1ff9a67005f96c5e1bc26a44778f911944054a25cf28bec5ce733  crates/yu-solver/src/candidate_context.rs
48094aff85175ef7b30d1ef8be0e8fc42d6e5282d0c4d562c4a730c13d401b25  crates/yu-solver/src/candidate_scheme.rs
2b0e46f28c328172477ac263360f4f3d01d27714dc62cd93235b8e3b1fe4e9ff  crates/yu-solver/src/shadow_apply.rs
```

The proof lane may apply to only this manifest and its seven immutable inputs.
No tests, builds, probes, Yulang/Yulang2/evaluator, Git, network, scratch or
unrelated paths were used. Source writes are STOPPED. Luna owns intake, review,
any future exact owner change, and Git integration.

## R176 final review and closeout

Fresh independent reviewer `/root/r176_final_review` returned **NOT_CLEAN for
candidate integration or parent closure**. It confirmed the scoped FreshUse
admission lemma: the stored cause and relation pass through exact Transport
validation, physical append/readback, and emission linkage for actually captured
bounds that restore successfully. It does not establish all original
source-to-Name/body coverage, later same-provider Apply, both ordered Replay
inputs, or consumed/reused port discharge.

Blocking review findings:

- `candidate_context.rs:3339` and `candidate_scheme.rs:1084–1138`: checking
  registration and enumerating visited local bounds do not prove every required
  original Name/body inequality reaches Capture or its shared anchor.
- `shadow_apply.rs:1290–1325,1426–1433` and `candidate_scheme.rs:600–626`:
  either-parent ancestry does not authenticate both ordered Replay premises;
  the later Apply relation is required inside an earlier Capture without a
  construction-generated bridge. Same-provider route identity is not retained
  through the checked association.
- `lib.rs:11593–11604,12517–12521` and `candidate_context.rs:2879–2984`:
  already-current pair dispatch can complete without four newly consumed
  FunctionPorts. The completed-map producer is outside the seven pinned owners;
  current/canonical/self/coalesced/rewritten discharge remains open.

Major resource finding: inline receipt growth and field-size subtraction do not
establish baseline layout/allocation equivalence. Completion capacity is retained
and omitted from the physical census; a successful optional reserve may consume
capacity needed by the next ordinary solver reserve. Arc-backed identity copies
still require headroom/drop/unwind premises. The local simulation remains
conditional on equal resource decisions and successful panic-free clones.

All parent/A/B/source-native/implementation/production gates remain OPEN. The
R176 candidate equals R174-v6 and remains NOT_CLEAN/unintegrated. Probe is
`NOT_RUN`; no tests, builds, probes, Yulang/Yulang2/evaluator, Git, network,
scratch or descendant activity occurred. Review observed 24 matching frozen
pins at entry/exit, including current hash `2a828b29…`; requested Sol/medium,
observed model/effort UNKNOWN, clock interval not provided by reviewer; full 480s charged because trusted
elapsed time is unavailable. Reviewer STOPPED.

Accounting: **4080/4200 seconds charged** including the full 240s closeout
because trusted elapsed is unavailable; 120s delta-review reserve expired
unused. R176 is **CLOSED_UNFINISHED_RESEARCH**. Luna remains sole owner of future
lease changes, integration and Git.
