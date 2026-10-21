# R177 — source coverage through consumer completion

Status: **revision 1 prospective-review candidate**. No proof or implementation
assignment starts until fresh exact-hash review is CLEAN and Luna activates this
contract.

Branch: `research/simple-sub-intrusion`  
Activation HEAD: `e9a7a4fef3d6872fa0596646393a7c0473b3687b`  
Fresh cap: **3000 seconds**, no carryover from R176.  
Parent theorem: `notes/theory/2026-10-15-computation-forwarding-preservation.md`,
SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`.  
Unchanged fixture: `tools/inference-playground/examples/r171-formal-name-forwarding.yu`,
SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.

R176 is closed `CLOSED_UNFINISHED_RESEARCH`. Its scoped result authenticates
FreshUse admission and physical append/readback only for bounds actually
captured and successfully restored. Preserve its frozen proof note
`6c6f8e59eac6ec2888ee04b96a67480a52d948bd6d50beb72ee369d2d9725e7f`, proof
handoff `b4f35119b7ed35f8181b58e1f50d5104b90154775f8bb8a0665d284d571a4bcf`,
implementation closeout `e69bc5ca3772a2930be2e7a23215afbe826ab589cc5fab69517e801dd295cc5c`,
and final review NOT_CLEAN. No parent, A/B, source/native or production gate
closed.

## Fixed outcome and success evidence

Trace the unchanged original source domain in construction order:

`source Name/body bound -> source emission/checking registration -> captured
seed/use -> authentic FreshUse admission -> physical restoration/readback ->
same-provider Apply -> both ordered Replay inputs -> consumed FunctionPorts ->
execution or current/reused-pair discharge`.

Use source correspondence, not endpoint matching or graph ancestry, to decide
whether every required original inequality reaches the actual consumer. Keep
provider/use identity, both ordered parents, arbitrary finite chains and
prefixes, shared xi, open incoming E, repeated/simultaneous entries, alternatives,
residual/scoped payloads, duplicate/canonical/self-pairs, zero products and
current/reused pairs in the original scope. The successful outcome is either
(a) a reviewed construction-to-consumer correspondence that discharges a
strictly smaller named premise of the original theorem, or (b) the earliest
precise missing constructor and its owning source location. Do not narrow the
source domain or promote a conditional lemma.

Resource erasure remains a separate OPEN obligation: inline layout and vector
capacity, allocation requests, optional reservation effects on shared allocator
state, Arc identity/refcount behavior, rollback, publication and unwind. Do not
infer noninterference from field-size subtraction, matching byte totals or
successful finite examples.

## Immutable inputs and scope

Luna froze two read-only ten-file source snapshots, all files mode `0444` and
directories mode `0555`:

- `/tmp/r177-inputs/baseline-7ec64a378/` — baseline commit
  `7ec64a3788175913a2be46331cf0f64c6bd5b407`.
- `/tmp/r177-inputs/v6-plus-construction-owners/` — R174-v6 candidate plus
  three construction owners, without changing the candidate bytes.

Both include the R176 seven owners plus `candidate_source.rs`, `candidate_call.rs`
and `candidate_intrusion.rs`. The three new owners are read-only discovery
inputs, not adopted production candidates or write leases. Their exact hashes
are identical in both snapshots:

```text
candidate_source.rs     cbc39315f4243b0bae1db74976cf94282bc94cd28b9eb463699c085f421065f7
candidate_call.rs       e038ad0dfc4b12bd0d513d6cd6b34cee6b2b062d8b33368bc1c0dcdef980d479
candidate_intrusion.rs  475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97
```

The full ten-file manifests are in the two proof/implementation packets. The
theorem, fixture, R175/R176 closeouts and snapshot modes/hashes are exact-hash
review inputs. New source-owner contents remain unread until CLEAN prospective
review. The mutable checkout is not a substitute for these immutable inputs.

## Continuing lanes

**Constructive proof — Sol/high, 1200s.** Use only the immutable snapshots,
theorem, fixture and frozen R175/R176 receipts. Establish the source emission to
capture coverage and continue through actual Apply, both ordered Replay inputs,
consumed ports and current/reused-pair discharge. Apply each valid result to the
original parent; otherwise identify the first absent constructor precisely.
Carry the resource question only as explicit premises and owner-specific TODOs.
Do not certify implementation or run compiler/evaluator evidence.

**Luna construction analysis — 600s.** Read the same snapshots and identify the
actual producer/consumer order, construction identities, current-generation
publication, rollback and discharge path. Produce an owner-specific design and
resource analysis. Current source status is **NO_SAFE_CODE_SLICE**. This grant
does not authorize code edits; a source-supported repair, exact write lease and
any new dependencies need a separate prospective review before implementation.
Inspect at least two actual owners before retaining NO_SAFE_CODE_SLICE.

Proof and Luna outputs are disjoint. After Luna freezes her analysis, proof
continues only against its already-pinned source inputs and may cite the frozen
handoff; any changed compiler bytes require a new candidate review.

## Exact output leases and prohibitions

Proof worker writes only:

- `notes/theory/2026-10-21-r177-source-consumer-construction.md`
- `tasks/agent-loop/inbox/20261021-r177-proof.md`

Luna writes only:

- `tasks/agent-loop/inbox/20261021-r177-implementation.md`
- this contract for primary-owned sequential revisions
- `tasks/agent-loop/current.json`

All compiler sources, tests, fixtures and other records are read-only. No code
write, staging, commit, push, test/build, probe, Yulang2/evaluator run, network,
nested CLI, scratch output or semantic promotion is authorized by this contract.
Unknown and legacy worker leases remain quarantined/held. All original parent,
A/B, source/native, implementation and production gates remain OPEN.

## Resources, review and stop conditions

The corrected fresh 3000-second allocation is:

| Work | Seconds |
|---|---:|
| Preparation and immutable manifests | 360 |
| Constructive proof | 1200 |
| Luna construction analysis | 600 |
| Prospective exact-hash review | 120 |
| Final independent review | 360 |
| Conditional delta-review reserve | 120 |
| Closeout and state synchronization | 240 |
| **Total** | **3000** |

Preparation is charged 360s; before prospective review, 2640s remain reserved.
After CLEAN review, proof and Luna grants are issued under their exact leases;
the final review and delta reserve issue sequentially. Unused reservations
expire. Unknown elapsed time charges the full grant. Astra 0, probes 0, no
carryover. Review checks exact frozen hashes/modes, preserved quantifiers,
disjoint leases, source-owner boundaries, budget arithmetic and unchanged gates.
Final review checks construction-to-consumer correspondence, resource premises
and every claimed parent application. Stop at the outcome, a genuine blocker,
budget, user STOP or session end; reconcile actual writer cessation before any
lease transfer.

