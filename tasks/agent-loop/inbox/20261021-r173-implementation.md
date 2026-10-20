# R173 Luna implementation packet — revision 2 candidate

Sprint `source-drain-attribution-and-consumer-join-20261021-r173`, contract
revision 2, SHA-256 `363135315afd7ee0fdfcc974e12e067c25959fb4475c44968a1a6fc7faed7b99`.
This is a sequential delta-review packet; it authorizes no compiler execution or
probe.

Proof baseline remains commit `7ec64a3788175913a2be46331cf0f64c6bd5b407`; R173
activation metadata is `9547edfc7`. R172 exact CLEAN code/query/harness review
remains in that sprint's implementation handoff. The original parent and
quantifiers remain frozen. Proof rev1 is bounded to original baseline owner bytes
and stopped after detecting candidate-context drift. It does not certify the
edited implementation candidate. Proof note SHA-256
`6a3fa980486875d671b6b2593baee910f1966467c8dec6980a36f29f9e1cb012`, proof
handoff SHA-256
`fe66540651d427f3b5ac32f63f82232898cdb7bf4e9d1e7cdea0a28c0825f887`.

Candidate snapshot at this delta boundary:

```text
99dc39e970b35f2d06a900826bf686ee5a76795430a3e4167ac5c64184da6af6  crates/yu-solver/src/lib.rs
ac1375954d0d310bbeaaccb09625dc4701dd1c25a050a67f1f203d91e9456b06  crates/yu-solver/src/candidate_context.rs
9569e7cc2ba7152cafe1273fba279a8511fe56aa39358798f3e4586c10ede225  crates/yu-solver/src/candidate_scheme.rs
13ae8de60293b91e24659090649ff84002f5632a8909451d3f7bd8492b61bea5  crates/yu-solver/src/shadow_apply.rs
```

After this delta review, continue the active implementation lease. These are an
intermediate candidate, not a new proof baseline. Final source review uses its
own frozen manifest.

Luna/high owns the bounded multi-step implementation across only the leased
paths: `lib.rs`, `candidate_context.rs`, `candidate_scheme.rs`,
`shadow_apply.rs`, the R173 diagnostic example, implementation note and this
handoff. The current candidate retains incoming relation, Replay acknowledgement,
created seed, selected relation and Origin index in the exact typed-drain frame.
It records the receipt after successful enqueue; failure before enqueue leaves
it unavailable. The frame already owns task, occurrence and cause. Continue by
proving and exposing this association without using it to select solver
decisions or alter publication. Never infer a missing field from equal IDs.
Keep selection, enqueue and drain completion as distinct phases, and account
for transaction rollback, repeated Origin ordinals and Replay-owned relations.

Build the borrowed query from owner records through the same provider's
Capture, FreshUse maps and exact forwarding Apply consumer. Preserve all
dependency alternatives and ordered Replay inputs. Report per-component
completeness; keep parent gates open. A conditional single probe is possible
only after the query discriminates every required link and a fresh reviewer is
CLEAN on exact source, code, harness and command pins. Otherwise record
`NOT_RUN` with the missing component. No tests, broad build, evaluator, Y2,
network, external oracle or behavior-changing implementation.

Requested Luna/high. Runtime observed model/effort remain UNKNOWN absent a
trusted receipt. The full 1500-second implementation grant is charged on issue;
no descendants. Stop if the certificate cannot stay behaviorally inert, a
necessary owner is not in the exact leases, failure-path semantics change, the
proof baseline is silently changed, or the sprint cap is spent. Preserve all
unrelated working-tree files. Fresh independent review follows frozen exact
hashes; only Luna stages and integrates reviewed R173 paths.
