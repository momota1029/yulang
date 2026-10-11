# Actual Local rollback: allocation-free snapshot restoration counterexample

Date: 2026-10-11
Status: independently reviewed bounded counterexample derivation from a frozen observation; no parent-theorem closure or production authorization.
Review: compiler-referee found no findings on the exact source/rollback bridge,
allocator interval, Oracle evidence scope, quantifiers, or exclusions.
Producer: leaf `/root/capture_rollback_counterexample_proof`; no delegation.
Baseline: primary-pinned `e28dfb61f`, branch `research/simple-sub-intrusion`.
Exclusive output: this note only.
Target: the frozen pre-repair implementation and recorded executable; the
concurrently repaired current implementation is outside this claim.

## Objective, frozen claim and authority

Determine whether the observed syntactic local function route refutes the
universal implementation claim that rollback restores every logged
capture-incidence snapshot allocation-free. Method: connect the recorded run
to the actual source action, transaction, mutation log and inverse insertion;
then instantiate the universal claim with one allocating inverse. No new
executable experiment is needed or performed.

Fix the implementation and linked runtime of the recorded experiment. Let
`s` range over source programs accepted by the exercised parser/HIR candidate
path; let `sigma` range over valid session states reached by their actual
preceding root-scheduled actions. Let `h` range over finite constructor-valid
capture admission/splice histories within an active Local route transaction,
and `f` over route-error exits exposing their rollback, including the supplied
post-sample fault-injection exit. Let `J(h)` be that transaction's ordered log
of exact `(row, Option<CaptureBucket>)` snapshots. For every inverse operation
`i` in the reverse traversal of `J(h)`, the required claim is:

```text
U: forall s, sigma, h, f, i in this domain,
   rollback restores the saved logical contents and
   inverse i completes without any alloc/alloc_zeroed/realloc request.
```

The concrete falsifier is `exists s,sigma,h,f,i` with a recorded request count
greater than zero during a saved `Some(bucket)` insertion. Success of logical
restoration does not rescue the zero-request conjunct. Each saved row, bucket,
record/link, source/view incidence and operation position stays distinct. This
local quantification does not rename or discharge the parent W/A3 binders or
its retained-frame hypotheses.

This freezes the structural claim about inversion of every valid logged
history. If a different claim quantifies **only** over failures reached without
test injection, the present record leaves its failure-reachability premise
unproved; that narrower domain must be stated explicitly, rather than inferred
from this witness. Likewise a theorem restricted to transactions entered with
an already suspended LocalUse frame is outside this witness.

Governing authority is the user-approved [private suspension contract](../design/2026-10-11-private-candidate-suspension-contract.md)
§6: route failure restores the pre-route state, and required storage is
fallibly reserved before its relying mutation. Section 6 does not literally
state U; U is the assigned storage/inversion obligation used to support that
failure contract. Refuting U does not refute the approved contract as a
semantic requirement. The user's accepted source correction requires a
syntactic function binding, which the witness preserves.

## Exact source and operational bridge

The frozen [observation record](../progress/2026-10-11-retained-local-capture-observation.md)
supplies the run and Oracle results. Define `ports` as 56 type positions in
order, two copies of `(int -> [tick, 'e{i}] ())` for each `i=0,...,27`, joined
by ` -> `. Substitute this text, rather than an identifier, into:

```text
act tick:
    our ping: () -> ()
my outer = { my bridge (consume:(ports -> ())) = consume; bridge }
```

The corresponding Yulang2 input uses `pub act`, `pub ping`, and
`my bridge(consume:...)`. The recorded Oracle checkout is
`a58eefc31e22141574b6f20c6a5748151c6d79f1`; its dump exited 0 with empty stderr
and displayed `bridge` as a syntactic function and detached local scheme.
This is imported evidence for acceptance/function form. It is not an equality
proof of complete Yulang2/Yulang3 inference results or evidence about rollback.

The shortest owning chain, at the frozen source hashes below, is:

1. `candidate_effect.rs:1709` `make_session` parses without structural recovery,
   lowers through `lower_module_with_local_source`, collects candidate mode,
   creates the session and starts its candidate graph. The test at `:1583`
   begins `Schedule::Root` and executes all actions before the final Local
   through `step_candidate_source(Support::READY)`. It checks that the scheme
   is installed and `local_use` is empty. The run records action 10, slot 0.
2. The local-name constructor at `candidate_source.rs:379` emits `Action::Local`
   for a resolved local whose initializer is no longer active.
   `step_candidate_source` at `:611` reads the actual next scheduled action;
   `execute_candidate_action` at `:680` calls `route_candidate_local`.
   The test enables its observer/hook immediately before this dispatch.
3. `candidate_scheme.rs:1354` `route_candidate_local_run` opens the real
   `begin_route_transaction` and invokes
   `finish_route_transaction_with_candidate_accounting(..., true)`.
   It captures the installed local graph, prepares one fresh use, pushes its
   LocalUse frame, then pops that frame for each atomic owner step and pushes
   it back before propagating the result. No manual outer transaction or
   direct incidence admission supplies the witness.
4. The LocalUse owner at `:1500` begins fresh bound restoration or steps a
   retained restoration/replay operation. `begin_candidate_fresh_bound`
   at `:1221` maps the captured bound and invokes
   `candidate_begin_bound_restoration`. That consumer at
   `candidate_extrusion.rs:659` calls
   `candidate_insert_bound_with_evidence(..., capture=true, ...)`; `:560`
   registers capture bounds. `candidate_effect.rs:550` recognizes a negative
   EffectRow-to-Allowance bound, obtains its canonical tail and invokes
   `candidate_capture_incidence`.
   This is source review of the constructor/consumer bridge; the observer
   does not identify each admission's precise bound or replay cursor.
5. Admission at `candidate_effect.rs:474` saves the previous bucket, reserves
   journal/map/key/record storage, logs `(tail,bucket)` and publishes the
   bucket/link/incidence mutation before its IncomingRoute sample. The hook
   at `:515` returns `IdentityExhausted` only after that sample succeeds,
   when a new-tail admission fills the map and follows an occupied-tail
   admission. It changes the exit, rather than constructing keys or replacing
   the map/hasher. Unrelated errors are rejected by the test.
6. `lib.rs:9208` handles that `Err` by calling `rollback_route_transaction`;
   `:9391` invokes intrusion rollback, and `candidate_intrusion.rs:104`
   invokes effect-algebra rollback. `candidate_effect.rs:266` consumes the
   actual saved bucket log in reverse, executing `insert(row,bucket)` for
   `Some` and `remove(row)` for `None`.

Capture uses an immutable session reference (`candidate_scheme.rs:268`);
fresh-use preparation constructs remaps/terms/views and imports evidence,
while the inspected physical bound admission owns capture registration.
The route-level reachability and transaction are observed; this attribution
of admissions to bound restoration/replay is the source bridge. In particular
`local_frame=false` observes an empty vector during the popped owner step. It
does not prove preparation caused the admissions or disprove LocalUse execution.

## Concrete witness and derivation

Take fresh-session index 1 of the recorded eight-session run. After 109 forward
admissions, the final two journal entries are an occupied row A=622 with a
saved `Some(bucket_A)` followed by new row B=623 with saved `None`. Their
actual four-operation suffix is:

| Operation | Saved snapshot | Map `(len, capacity)` before | After | Measured inverse insertion requests |
| --- | --- | --- | --- | --- |
| Admit A=622 | `Some(bucket_A)` | `(55,56)` | `(55,56)` | not measured |
| Admit B=623; injected error after successful sample | `None` | `(55,56)` | `(56,56)` | not measured |
| Reverse B: remove | `None` | `(56,56)` | `(55,55)` | not measured |
| Reverse A: insert exact saved bucket | `Some(bucket_A)` | `(55,55)` | `(55,112)` | **1** |

Forward event counters and inverse `None` counters are hardcoded zero in the
observer; they are not measured allocation-free intervals. Only the last
row's positive count is needed for the refutation. The public capacity values
are observables, not assumed raw-table growth credit or a reconstructed layout.
The observed suffix is not asserted to be a minimum source program.

At `candidate_effect.rs:270`, the cfg(test) observer begins immediately before
the production `HashMap::insert`; its `end` precedes event-vector append.
The wrapper at `:49` counts same-thread `alloc`, `alloc_zeroed` and `realloc`
calls while active and delegates to `System`. TLS initialization/reset,
checkpoint copies, event allocation and printing are outside that interval.
The map is `HashMap<u32,CaptureBucket>` with copied scalar bucket contents and
the ordinary hasher, without a user allocation callback. Thus the counted
request belongs to inversion of this saved snapshot, rather than probe output.

Instantiation of U with this `s,sigma,h,f,i` requires count zero. The imported
run gives count one. Hence U is false on the tested runtime and permitted
fault-prefix domain. This is an independently reviewed bounded source-qualified
counterexample derivation from execution evidence and exact source
correspondence. It is not an all-source mathematical theorem. The earlier
[HashMap reduction](../progress/2026-10-11-capture-map-inverse-capacity-proof.md)
explains why replacement can allocate before key lookup; that reduction is
supporting context, not a necessary assumption for this direct positive-count
argument. No raw hash placement need be reconstructed to use the actual run.

All eight sessions reached the hook; sessions 1,2,4,5,6 each counted one inverse
request, and 0,3,7 counted none. These are uncontrolled RandomState sessions,
not reproducible seeds or a probability estimate. Every target passed the
recorded checkpoint inventory and explicit logical map/record/key/context,
source-frame and route-count restoration assertions. Those assertions concern
their implemented inventories; they do not prove byte-identical state or
general rollback correctness. Allocation succeeded; allocator failure was
neither induced nor observed.

## Boundary, economy and next owner

The failure prefix is constructor-valid and reached by an Oracle-qualified
function through actual scheduled Local execution. The return point is
test-injected after successful sampling. This suffices to refute unconditional
allocation-free restoration of every such logged snapshot. For a claim whose
domain excludes injected faults, the missing premise is a naturally occurring
production error at this or an equivalent prefix preserving the allocating
inverse state; owner: the route/error and capture mutation seam. No statement
here asserts that premise.

For a theorem requiring an already retained/suspended parent on transaction
entry, the additional missing premise is reachability of this allocating
history from that entry state; owner: the retained Local lifecycle lane.
This run starts fresh and never pauses. It therefore supplies storage feedback
without closing original W/A3 or the retained-frame theorem.

The allocation-free inverse obligation is A storage/failure correctness under
the existing contract. Its decisive storage premise has an observed falsifier
for the stated domain; another live-length proof or repetition of
`try_reserve(1)` cannot establish U. Under the proof-obligation-economy rules,
the next action is primary adjudication and authorized repair at the owning
capture-map mutation/inverse storage seam, followed by independent review.
No source restriction, additional annotation or semantic weakening is proposed.

Other maps, absent-key reinsertion witnesses, allocator exhaustion, pause/resume,
all rollback histories/platforms, retained-byte/accounting inequalities,
complete Call, effect hygiene, soundness/principality, full inference and F5
cutover remain unverified by this note. No proof or production gate is closed.

## Frozen dependencies, checks and resources

Paths below are repository-relative; compiler files are under
`crates/yu-solver/src/`.

| Dependency | SHA-256 |
| --- | --- |
| `candidate_effect.rs` | `da3adca5f3ac53c486fd542d7684641adfd4568c19941989282c0820dae8edd9` |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| observation record | `61174f1d4e71df401e88116c9cc0ca2090fb4e154ed6c4baac8c1833711934df` |
| suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| earlier HashMap reduction | `b765a6cbbf3061b8ef5c7bc3bfe67122cd5c599b243bfaa00b9e4ce8e7db3569` |

The final dependency recheck at 02:48 UTC found `candidate_effect.rs` changed
externally from the frozen pre-repair hash above to
`ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df`.
The primary confirmed this was the authorized concurrent occupied-key repair.
All other direct dependency hashes remained unchanged. Source locators and U's
refutation in this note refer to the frozen pre-repair source/evidence;
the repaired current tree is neither refuted nor certified here. Rechecking
that repair is owned by the primary's implementation/verification/review lane.

Checks in this packet: `cat`/`sed` policy, skill, role, governing record and
source reads; `rg -n` owning-symbol searches; `sha256sum` dependency checks;
new-path existence check and final note/lease inspection. No Git operations,
tests, builds, Oracle reruns, repeated probes or measurements were performed.
The recorded experiment's exact Cargo command and Oracle command remain in
the input record; their results are imported, not claimed as this leaf's runs.

Resource use: one leaf; lightweight read processes only, no Cargo/probe/build
processes or descendants; CPU/RSS unmeasured. Normal configured/requested
proof policy is `gpt-6.1-sol/high`; launch arguments and observed role/model/
effort metadata are unavailable to this leaf and remain unknown. No Astra
escalation or configuration edit occurred. The primary remains verification
and integration owner. Stop condition: one exact allocating witness and its
scope boundary derived; output frozen for primary review.

## Commit packet

- Exact completed lease: `notes/theory/2026-10-11-capture-local-rollback-allocation-counterexample.md`.
- Baseline SHA as supplied: `e28dfb61f`; no Git operation to expand it.
- Changed dependency hashes: none authored; external `candidate_effect.rs`
  change `da3adca5f3ac53c486fd542d7684641adfd4568c19941989282c0820dae8edd9`
  to `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df`
  belongs to the concurrent repair and is excluded from this claim.
- Claim/review status: independently reviewed bounded counterexample derivation;
  no self-certification or parent-gate promotion.
- Checks already run: static reads/searches, dependency hashes, lease existence
  and note inspection; no new executable verification.
- Proposed checkpoint message: `research: derive actual Local capture rollback allocation counterexample`.
- Shared-record deltas left to primary/curator: record the refutation of U on
  the source-qualified injected-fault domain; retain the non-injected-failure
  and retained-entry boundaries, original W/A3 and other-map storage obligations;
  route capture storage repair to its authorized owner. No shared record edited.
