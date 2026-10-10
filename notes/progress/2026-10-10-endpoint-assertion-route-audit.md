# Endpoint assertion after parent/copy intrusion

Date: 2026-10-10. Status: frozen, unreviewed, non-authoritative research.
Producer: `/root/endpoint_assert_observer`.
Baseline: `4dc9a2f853aa7de4082dea05576b9619914d4532`.
Exclusive write lease: this note. Method: one bounded existing-binary GDB
observation of the previously recorded exact source; no build or test completion.
Claim class: bounded execution characterization, with a source ownership audit.
No global restoration-R, impossibility, soundness or production closure claim.

## Objective, authority and exact premise

Classify the recorded assertion as stale retained endpoints after expected
equality, incorrect RelationId association, or unclassified. Governing sources
are contextual-attachment-admission design §§3.1–5 (exact annotation identity,
ordered replay, retained contexts and parent/copy obligation transfer), and
parent-copy-scc-intrusion's Selected operation and compiler responsibility
(equate actual recorded parent/copy pairs in one SCC). These meanings are
preserved. Rules research-lab, design-authority, git-concurrency and the
yulang-proofs skill were read. Constructive proof and independent review remain
primary-owned; this producer neither delegates nor certifies its own output.

The exact input is copied from bridge-result-type-route:

```yulang
act E
my left (f:int -> ['r] int) g = { my bridge (consume:(int -> [E, 't] int) -> ['x] int): ((int -> [E, 't] int) -> ['x] int) -> [E, 'x] int = { my cb z = { my old = f 1; consume cb }; my feed = g bridge; consume cb }; bridge }
```

Input: 230 bytes; SHA-256
`3441ca38380ec073726a35d2273267d5c6839bab11573eb3367847995fe55256`.
This is one existing root, with no minimization or new variant.

## Discriminating observation

**Classification: a retained relation and its raw work item agree, but both
retain the pre-equality upper row58 after an actual parent/copy merge into44.**
The assertion's stored side is stale relative to canonical session identity.
There is no task/RelationId endpoint association mismatch at this observation.

At `candidate_context.rs:1846`, immediately before the assertion:

| Observed field | Value |
| --- | --- |
| Raw task | `Effect(EffectRow(27), EffectRow(58))` |
| Active TypedWorkItem | the same raw task, `Some(RelationId(270))` |
| Stored key at RelationId270 | `Effect { lower: EffectRow(27), upper: EffectRow(58) }`, ContextId0 |
| Canonical task endpoints | `(27,44)` |
| Representatives | rep44=44; rep58=44; rep27=27 |
| Context processing | `Some(RelationId(270))` |
| Task processing | `Some(Effect { lower:27, upper:58 })` |
| Intrusion generation / errors | 8 / 0 |
| Remaining worklist | length22, head36, capacity43 |

The observer stopped at the **first unequal stored/canonical Effect pair** it
encountered, after 209 executions of the assertion breakpoint. GDB then printed
the stack and exited. It did not continue through the panic or complete root
inference. Zero prefix errors do not establish successful publication.

Merge entries were observed in this order:

```text
entry generation0: 50 -> 27, Negative,target1, processing RelationId268
entry generation1: 52 -> 46, Positive,target1, processing RelationId268
entry generation2: 53 -> 46, Negative,target1, processing RelationId268
entry generation3: 56 -> 23, Negative,target1, processing RelationId268
entry generation4: 58 -> 44, Negative,target1, processing RelationId268
entry generation5: 59 -> 6,  Negative,target1, processing RelationId268
entry generation6: 60 -> 5,  Negative,target1, processing RelationId268
entry generation7: 61 -> 23, Positive,target1, processing RelationId268
```

The first merge of any pair is50→27 at generation0. The first merge affecting58
is the fifth entry,58→44 at generation4. At its entry rep58=58, rep44=44;
at `candidate_intrusion.rs:593`, after the forest write and before contextual
bound canonicalization, rep58=44, rep44=44. The retained Parent record itself
is `(copy58,parent44,Negative,target1)`. Before that write, physical outgoing
direct-row bounds plus actual Support/Allowance view-tail edges give:

```text
reach(44) = reach(58) =
{5,6,23,25,27,30,33,37,41,44,46,54,55,57,58,59,60,61,62,69}
```

Thus this specific equality follows the selected actual-parent/same-SCC
operation under the inspected graph-edge contract. Parent provenance and
capture incidence were not added as graph edges. This check shares the
compiler's SCC edge interpretation; it is not an independent semantic oracle
or a theorem validating that interpretation for all programs.

## Actual owning route and static bridge

The failing stack is:

```text
candidate_context_execute                         candidate_context.rs:1846
constrain_live_item_with_inferred_entry closure    lib.rs:11861
constrain_live_item_with_inferred_entry            lib.rs:11827
constrain_live_item                               lib.rs:11805
constrain_live                                    lib.rs:11792
constrain_live_value                              lib.rs:11783
admit_candidate_value_link (slot40)                candidate_scheme.rs:1114
candidate_local_annotation closure                candidate_effect.rs:1020
candidate_local_annotation (slot0,level2,boundary1) candidate_effect.rs:1003
execute_candidate_actions                         candidate_source.rs:569
execute_candidate_source_root                     candidate_source.rs:545
existing host                                    candidate_effect.rs:1878
```

The initial top-level work item is ValueRow5→NegativeFunction(index395), with
no supplied RelationId. This is an ordinary local-annotation worklist route;
`candidate_restore_bound` is absent from the active stack. The packet's
`candidate_restore_bound.rs:632–638` locator resolves to the function in
`candidate_extrusion.rs:632–638`, not a separate file.

Static source facts explain the invariant boundary without proving the exact
creation history of270:

- `candidate_context_pair` at1595 canonicalizes endpoints through session
  representatives. The assertion compares this result with the stored key.
- `State::relation` at1422 interns the supplied pair/context and retains that
  key; it does not recompute old keys when representatives change.
- Intrusion writes the representative forest, then calls
  `candidate_context_canonicalize_bounds` at593. That method creates canonical
  child relations and Derived dependencies for bound fibers; its inspected
  body does not rewrite existing relation keys or queued work items.
- `enqueue_item` at `lib.rs:12123` retains an already supplied RelationId and
  raw task. The drain at11861 passes that item to the assertion directly.
- Ordinary `candidate_replay_bound` publishes via `enqueue_item`; restoration
  publishes via `constrain_live_item`. Both use the common replay producer
  at `candidate_context.rs:1982–2029`. No restoration call was observed in
  the failing active stack.

Consequently the observed failure is an endpoint identity lifecycle seam.
Which exact producer created/enqueued270, and whether270 existed before the
58→44 forest write or was later selected through an old retained key, remain
unverified. The observation does not select an implementation repair.

## Commands, resources, failure conditions and omissions

The frozen runner
`/tmp/yulang-bridge-return-annotation-selective-route-20261010/run.py` was read
only. Its prefix before `args=['timeout'` was evaluated in Python memory to
obtain the existing binary locator. One `subprocess.run` launched:

```text
timeout 45s gdb -q -nx -batch -ex <each command below> <existing binary>
```

GDB commands set pagination/debuginfod off, print-elements12, break make_session,
and run the existing host
`candidate_effect::tests::formal_and_whole_annotation_share_tail_in_the_returned_effect_fiber`
with `--exact --test-threads=1`. In C language mode, malloc8192/memcpy supplied
only the exact source bytes, updating text.data_ptr/text.length and the
prepared rdi/rsi. Rust mode then installed Python observers at merge entry,
intrusion.rs:593, context.rs:2029 and context.rs:1846, followed by continue and
`bt 16`. No solver state, transition, endpoint or constraint was injected.
The Python observer read the existing Vec storage and representative forest;
the endpoint observer compared the stored pair with manually canonicalized
raw Effect endpoints, and stopped on inequality.

The replay-publication observer failed because its closure's `self` was not a
pointer and the helper unconditionally dereferenced it. Those observer failures
left relation-generation IDs and replay input heads inaccessible at that
breakpoint. Merge and assertion observers succeeded. No second launch was
made. The raw queue's remaining member contents were not decoded. Exact270
creation/enqueue timing, its derivation parents, and all preceding restoration
activity therefore remain inaccessible in this run. The complete stack and
decisive endpoint/merge observations were retained without output truncation.

Coverage: exactly the assigned source prefix; no seeds, ranges, mutations,
external Oracle, completed host assertions, successful publication,
rollback/retry, repair validation, omitted-fiber or rescue theorem. No
performance samples. Eight merges and one first mismatch were observed.

Resource envelope: one GDB launch/inferior, one CPU affinity, 1.5GiB address
space, CPU55s, inner timeout45s, Python timeout50s, within the60s launch budget.
Observed wall1.583216353s, user1.288590s, system0.289967s, peak351224KiB;
returncode0 denotes an intentional breakpoint stop, not a passing test.
Captured stdout22348 bytes, SHA-256
`9de519ddfcd8b76dc218aea9a4b944475f41c497e33cf369652d9978c646ea6b`.
Static reading/report wall-time was unmeasured. Zero builds, Git mutations,
new tests or parallel heavyweight processes.

## Frozen dependencies and next action

HEAD remained the assigned baseline. Narrow Git diff against that baseline was
empty for the inspected source/design/input-note paths. The following SHA-256
dependencies matched before the launch and at freeze; none was changed:

```text
3b219b51ed8aba6ffc85675fd1d500b901a6f63b31325a85a586d688eee3515a  candidate_context.rs
3fd1c7234c38013343e1c2e72bfed06c4eecdf7173e27d7581e11d6df84f0b3a  candidate_extrusion.rs
aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0  candidate_intrusion.rs
9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1  lib.rs
717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc  contextual-attachment-admission design
8ae4348a93dce6df1852a34b2294ebc5e4e256d8b018c1f6eaad42c502470a8e  parent-copy-scc-intrusion design
c160e6409dedcf1a9c62856cf1695aa26e0b53418b851854d57f12d23461c8ad  bridge-result-type-route note
02135a9533f33c0f877456595741ce05b07ea1d37510f3debea8931c513ebe99  existing run.py
7aee4053118d02e626d70695433018c356105e8e7663e3f9776b5d922c4a4ec3  existing binary
```

Recommended next action: primary assigns an explicitly authorized owner audit
and repair of queued relation endpoint transport across intrusion, preserving
context/derivation identity, with this exact source as the focused regression.
The repair owner should resolve270's producer before choosing the seam; this
research lease does not authorize that implementation.

Commit packet: exact leased path
`notes/progress/2026-10-10-endpoint-assertion-route-audit.md`; baseline
`4dc9a2f853aa7de4082dea05576b9619914d4532`; changed dependency hashes none;
frozen, unreviewed, research-only. Checks already run: narrow static owner reads,
baseline-path diff, nine before/final dependency hashes, one bounded GDB launch
with successful merge/assertion observation and failed replay observer.
Proposed checkpoint: `research: classify stale relation endpoints after intrusion`.
Shared-record deltas left for primary/curator: retained270/raw task agree;
58→44 is an actual qualifying parent/copy merge; failing route is ordinary
LocalAnnotation; exact producer chronology remains open; no change to R or
any theorem status. No shared records or question-board bundles were edited.
