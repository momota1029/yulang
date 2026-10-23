# R339 — K0 native retirement and Value-call prefix simulation

**Revision 2.** Sequential amendment from contract rev1 SHA-256
`e74ea60ec6c9a7fee246fc9bca9ad0bfae2712c291fe570c1f5bbd25f1aac3fc`. Rev1
was acknowledged by both lane owners before this file was created. This revision
records the selector-approved exact R338 review input, the already reached D2
source owner, and the completed 150-second review disposition. It changes no
proof scope, source-write authority or total sprint cap.

**Status:** ACTIVE after R338 closeout. Fresh sprint; no R338 budget or
authority carries over. Primary `/root` owns this contract, the D3 source
artifact, current state, review adjudication and Git integration.

## Original objective and audit authority

The unchanged parent objective is the full Yulang2/Simple-sub source/native A/B
theorem, catalog and implementation correspondence. Follow the user-directed
`docs/Yulang Simple-sub 拡張：全体証明への移行監査・証明設計.md` (SHA-256
`b720fc938423bea1b677f7121653e2452b0fb0b9bb2919e9d38c7fccbee64895`). Its K0
contract is the ordinary single-root, nonrecursive, selected-definition core;
source typing and `H(S)` are independently defined; S0 is the first whole
target. F and L0 remain bounded results from the audit and inherited R336–R338
evidence. This sprint does not re-prove or enlarge them. The audit expressly
allows D3 to proceed before D2 closes, so this sprint advances both in parallel.

## Bounded outcomes

### D2: one obligation-retirement family

Pin `H(S)` to the audit/R338 independent interpretation, including current,
pending and processing logical obligations. Establish or refute that an actual
K0 obligation `q` removed from the live work representation across the
**cache-current check → replay-child acknowledgement → typed-drain terminal / frame
retirement** remains entailed by the remaining interpreted theory. Derive this
from the source owners and transitions; a completed bit, duplicate key or
historical `ConstraintStore` receipt alone is not evidence that `q` remains in
`H(S)`.

Keep admission separate. For either fresh or duplicate admission receipt, the
R338 correction is `H_after = H_before ∪ {q}`. Equality requires a separately
established premise `H_before ⊨ q`; the correction is pending a narrow fresh
delta review and is not independently accepted by this contract. It does not
block the D2 retirement investigation.

The producer may establish a conditional theorem for the named lifecycle or
return the first source-qualified counterexample/missing owner. No full N,
cache-coverage, temporal-coverage, W, Z or S0 conclusion follows.

### D3: actual Value-closure Call prefix

The primary constructs a bounded typed-configuration/continuation relation for
one authentic K0 source `Apply f a` and its actual selected-definition runtime
entry. Define the source typing and runtime realization independently of
successful execution. At the call seam, retain the actual callee `ValueHandle`,
its `ExecutableValue::Closure` and saved capture environment, the caller
environment, the whole argument `Delay`, invocation ID/owner and frame stack.

Trace the source/runtime counterparts through:

1. HIR `Apply` to runtime `Instruction::Apply`;
2. callee evaluation and actual closure-handle lookup;
3. creation of `Delay { code: a, environment: caller_environment }`;
4. fresh invocation and `ReceiverReturn` for that same handle/site;
5. entry through `ValueEntry`, forcing the delay under the caller environment;
6. binding the received value to the exact closure parameter in its saved
   environment and starting the exact closure body.

The source `SourceSite` is not closure identity. Distinct closures from the same
Lambda occurrence may carry distinct capture environments. The simulation must
preserve that distinction. Owner restoration on normal return is optional and
only included if its premises are established in this packet.

This is a prefix lemma for a Value-entry closure, not full M, progress,
preservation, accepted-run soundness or runtime safety. Keep symbolic effects,
budget pauses and possible divergence. If a K0 Apply case requires an
unavailable canonical-form or realization supplier, isolate that exact premise
and leave the broader claim OPEN; do not assume runtime completion or type
safety to define realization.

### Shared S0 seam

The lanes share only the unchanged K0 source judgment, authentic source
identities and the audit's root Value/body Effect endpoints. D2 does not supply
D3's runtime realization. D3 does not supply native `H(S)` solution existence
or N. Preserve the existing R336 D1 conditional assumptions and R337 ordinary
context premise; do not promote their conjunction to whole S0.

## Fixed inputs and exact source pins

- Branch/head: `research/simple-sub-intrusion`,
  `f647390d6a3502c0d8814d46870d55685cee1753`.
- R336 rev4 contract: `080ab51650f88ddb7030e2a9bcb0ebfc9cc9b62de29204910e888365f7d03118`.
- R336 integrated proof: `4bcbe71ec9f2372baca884e3db737c16fc19ad2a51103965ade5ca4c2ecf4973`.
- R336 independent review: `d03b7a23bcec2bd0575bf391342f92353b46b840cbcfa70deea7500786fd892e`.
- R337 contract/proof/census: `0d71e3c740aa3d48667e3a9d62d15b835084a432e394fe79cc30d2b9d4cc9a3e`,
  `e14b8125a505c3001021396b8c6e949e3b0a58f61ecf2785f915dbdde65dfc62`,
  `771c3c8ab2a69336579c78a7583097b8d1839bf0d6fe97f2e69da27e77500e6a`.
- R338 contract/proof/census rev2/reviewed census rev1:
  `d742fa449c81b8b3cc918f53f93fc462dccb98565a2ed817e0b64162919ee403`,
  `f438939f99c212324a397f527d46d4a4ab565733e4b2e9e2ae55254e96ca9bf0`,
  `56174af37c13d2e6ac846b84c3fd71075bceefb8b05474c1f8b3d6d5b2c50ac9`,
  `1361b0223e8950c3e6546f1cbcb9cd25bd7a0ca038511f7c55cad29d3659fa6d`.
- D2 source hashes: `crates/yu-solver/src/lib.rs`
  `ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07`,
  `candidate_context.rs`
  `33af2efb6ed782e4f143cccff03c62087e6ba8d0fbe90415846537fc2a08cec5`,
  `candidate_intrusion.rs`
  `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`,
  `candidate_extrusion.rs`
  `80f126e9c77d1b3d8486c01b4f35a6852f4d466f99daed45ea4e19a598d59d61`, and
  `candidate_effect.rs`
  `d156fdbf0300387a5aa036053a2cc7eeb6312a803aaf38838e30dd2731ca4945`. The
  latter is pinned because lines 502–518 define the processing/task/enqueue
  evidence owner actually reached by the contracted D2 retirement trace.
- R338 rev1 review snapshot: `tasks/agent-loop/review-inputs/r339-r338-census-rev1.md`,
  SHA-256 `1361b0223e8950c3e6546f1cbcb9cd25bd7a0ca038511f7c55cad29d3659fa6d`,
  byte-for-byte from Git blob
  `3a0cfbccd5376ee4cf20adab84c3a6db1c19acb1:notes/theory/2026-10-23-r338-k0-state-source-census.md`.
- D3 source hashes: `tools/inference-playground/src/runtime/program.rs`
  `df58f9a1d60e39fafe6d85b1e50331b35fde2a9142a2eaea84ad028d3048fdb0`,
  `machine.rs`
  `02adc26bcd58cca488a40e78289a264751146d7900c2897db19068b279a8d840`,
  `literal.rs`
  `2fff177a7ba0cabb4930251e1facc8f9be701ff3ec7baa695ce4c182fa1da35f`,
  `receiving.rs`
  `2170a3bcbc6710ce3fbf721a05129117f8266b9ecf21c67136db918815303551`.

Re-verify all inherited documents and source hashes before adjudication. Source
files, HIR and runtime are read-only. Extend the manifest only for a named owner
actually reached by the proof, with reason and hash. The user audit remains
untracked and is never staged.

## Lanes and exact leases

**Constructive D2 lane:** requested `prover`, Sol/high, maximum 1,200 seconds.
It owns only:

- `notes/theory/2026-10-23-r339-k0-obligation-retirement.md`
- `tasks/agent-loop/inbox/20261023-r339-k0-retirement-prover.md`

**Primary D3 lane:** `/root`, maximum 1,200 seconds. It owns only this contract,
`notes/theory/2026-10-23-r339-k0-machine-call-simulation.md`,
`tasks/agent-loop/current.json`, and the one-time exact-byte review-input
snapshot `tasks/agent-loop/review-inputs/r339-r338-census-rev1.md`; that snapshot
is frozen after creation.

The R338 admission delta received a separate 150-second review allocation.
That allocation is fully charged and its disposition is **OPEN / incomplete**:
the reviewer checked the amendment semantics but reached the cap before the
exact rev1/rev2 byte comparison. The immutable input is now available at the
pinned snapshot above, and its bytes match the pinned digest. The prior
allocation is not renewed or reused in R339; keep the R338 admission correction
OPEN pending a separately authorized future review.

After both R339 artifacts freeze, one fresh non-contributor
`compiler_referee`, requested Sol/medium, gets at most 750 seconds for separate
D2 and D3 dispositions on the frozen R339 bundle. The reviewer has no write
lease and must not be a producer/primary contributor. Integration/state
synchronization reserves 300 seconds.

Fresh cap: **3,600 seconds total** (D2 1,200 + primary D3 1,200 + R338 delta
review 150 + R339 independent review 750 + integration 300). Charge grants
conservatively; observed model/effort remains UNKNOWN unless runtime reports
it. No Astra, no carryover, no renewal and no second heavy process. Preserve the
three legacy `UNKNOWN` quarantined identities and leases.

## Review, falsifiers and stop boundary

Review D2's exact `H(S)` and removed obligations at cache skip, acknowledgement
and terminal retirement; challenge any use of historical admission, a completed
label or a cache key as semantic evidence. Review the R338 delta as a distinct
claim against rev1/rev2; it gates acceptance of that correction only.

Review D3's independent source judgment, realization relation, actual closure
handle/environment, caller argument environment, parameter/body identity,
owner/frame sequence and exact program/runtime source mapping. A different
closure, captured environment, argument, binder or invocation falsifies the
claimed correspondence. Missing canonical-form/realization suppliers remain
OPEN.

Stop this bounded packet on source/input hash mismatch, unknown writer, exact
source-qualified counterexample, an accepted major/blocking review finding,
resource cap or user STOP. Consult the selector on a substantive
counterexample/missing owner, dependency/lease change, frozen integration seam
or cap. No code change is authorized; report `NO_SAFE_CODE_SLICE` absent a
source-qualified defect. No tests, Cargo/builds, probes, descendants, external
contact or worker Git. Root owns exact-path staging, commit and non-forced push
after review and integration. No broader N, W/Z/S0, principality, original A/B,
catalog or production gate closes automatically.
