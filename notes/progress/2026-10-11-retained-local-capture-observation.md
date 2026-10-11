# Actual Local route: capture-map inverse allocation observation

Date: 2026-10-11
Status: independently reviewed, non-authoritative bounded source-correspondence experiment.
Producer: `retained_local_capture_probe`, complementary researcher lane.
Baseline: `0d643a144baec574881af97ff82d841b5352a518`, branch
`research/simple-sub-intrusion`.
Authority: private candidate suspension contract §6; the user's correction
requires a syntactic function binding rather than an expansive annotated value.
Review: compiler-referee and spec-auditor found no findings on the frozen code/note.
The reviews cover the actual Local route, rollback comparisons, allocator
interval, Oracle source form and claim scope; they do not certify general
rollback, suspension/resumption, or theorem closure.

## Objective and method

Determine whether an Oracle-valid local function binding reaches the earlier
occupied-A/new-B/remove-B/restore-A capture-map suffix inside the actual
root-scheduled `Action::Local` transaction. The earlier
`2026-10-11-capture-map-native-probe.md` called `candidate_formal_annotation`
inside a manually opened transaction and explicitly left this seam open.

The new ignored test is
`candidate_effect::tests::retained_local_capture_inverse_observation`.
It parses and lowers source, starts its actual root schedule, and steps the
source owner until the final local `bridge` use. All preceding actions,
including formal annotation, Lambda construction and local installation,
run through `step_candidate_source`. Observation and the existing test-only
failure hook are enabled only immediately before the final `Action::Local`.
The next `step_candidate_source` dispatches that action. There is no manual
formal constructor call and no outer synthetic route transaction.

One source size, 28 distinct tails with two positions per tail, is sampled
in eight fresh sessions. The normal `HashMap` and its uncontrolled
`RandomState` are used. No direct incidence admission, row-key substitution,
seed sweep, table layout assumption or allocator failure is introduced.

## Oracle-qualified source

For each `i` from 0 through 27, repeat `(int -> [tick, 'e{i}] ())` twice in
`ports`, joining those 56 positions with ` -> `. The exact Yulang2 source
template is:

```text
pub act tick:
    pub ping: () -> ()
my outer = { my bridge(consume:(ports -> ())) = consume; bridge }
```

Here `ports` denotes that generated text, not a source identifier.
The binding under investigation is the syntactic local function `bridge`;
`outer` is the enclosing block. No `my ans: [E] int` form is used.
Yulang3 uses `act tick`, `our ping`, and the parser-required space in
`my bridge (consume:...)`.

The frozen Oracle checkout is `/tmp/yulang2-oracle-read`, commit
`a58eefc31e22141574b6f20c6a5748151c6d79f1`. One dump was run, with no
scratch source file or build:

```sh
python3 - <<'PY'
import subprocess, time
ports = ' -> '.join(f"(int -> [tick, 'e{i}] ())" for i in range(28) for _ in range(2))
source = f"pub act tick:\n    pub ping: () -> ()\nmy outer = {{ my bridge(consume:({ports} -> ())) = consume; bridge }}\n"
start = time.monotonic()
r = subprocess.run(['/tmp/yulang2-oracle-read/target/debug/yulang', '--no-prelude', '--no-cache', 'dump', '/dev/stdin', '--poly'], input=source, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=30)
print(f'oracle_exit={r.returncode} wall_seconds={time.monotonic()-start:.3f} source_chars={len(source)} tails=28')
print(r.stderr[:1500])
print(r.stdout[:5500])
PY
```

Result: exit 0, empty stderr, 1,642 source characters, 0.191 seconds observed
wall time. The dump prints the block's `bridge` binding as
`fn p1:d4:consume -> ...` and a detached `my d3:bridge:` scheme with effect
variables such as `['a#0[tick]]`, `['a#1[tick]]` and paired returned
`[tick; 'a]` positions. The captured display is truncated to 5,500 characters;
the entire stdout was collected before truncation. This establishes Oracle
acceptance and the syntactic/generalized local function form, not equality of
the complete Yulang2 and Yulang3 inference results.

Oracle independence is limited and explicit: Yulang2 is independent evidence
for source acceptance/function generalization. It does not exercise Yulang3's
root scheduler, Local transaction, rollback, allocator or contextual rules.
The Yulang3 experiment uses the actual implementation of those mechanisms;
it is an observation of that implementation, not an independent model of its
source rules. Both inputs share the authored function type template and the
accepted function-binding meaning.

## Actual transaction and source correspondence

The source cursor reaches action index 10, local slot 0, with the local scheme
installed and no resident `local_use` frame. Its capture-incidence map begins
at `(len, capacity) = (28, 56)` in every sampled session.

The owning chain is:

```text
step_candidate_source
  -> execute_candidate_action(Action::Local)
  -> route_candidate_local
  -> route_candidate_local_run
     -> begin_route_transaction / finish_route_transaction_with_candidate_accounting
     -> capture_candidate_graph
     -> prepare_candidate_fresh_use
     -> push LocalUse
     -> pop frame / step_candidate_local_use / push frame before fallible return
        -> begin_candidate_fresh_bound or step bound restoration/replay
        -> candidate_insert_bound_with_evidence
        -> candidate_register_capture_bound
        -> candidate_capture_incidence
```

`capture_candidate_graph` uses immutable session access while collecting the
graph. `prepare_candidate_fresh_use` reconstructs row/term/view identities,
renames contexts and imports evidence; its inspected constructors do not
admit physical capture bounds. A negative EffectRow/Allowance bound is
registered when physical bound restoration calls
`candidate_insert_bound_with_evidence(..., capture = true, ...)` in
`candidate_extrusion.rs`. This provides source/caller correspondence for
admissions during LocalUse execution, including its nested replay consumers.
It does not identify the exact bound cursor of each logged admission.

The auxiliary event field `local_frame` observes only whether the
`local_use` vector is nonempty at admission. It is false for every recorded
admission, and the printed `retained_admissions=0` therefore means zero
**vector-resident** admissions. The route deliberately pops its LocalUse
frame while executing an atomic owner step and restores it before handling
the result. Thus this field does not discriminate preparation from execution
in the popped LocalUse owner. The actual Local transaction is directly
observed; LocalUse-vector retention itself is not observed. The LocalUse
owner attribution above is a source correspondence argument, not a positive
retention observation. This experiment does not cover a pause/resume or
failure beginning from an already suspended retained frame.

The existing hook injects `IdentityExhausted` only after a successful
IncomingRoute resource sample when a new-tail admission fills the map and
the preceding recorded admission used an occupied bucket. It is enabled
only for the actual Local dispatch. Earlier unrelated failures fail the
test, rather than counting as targets. No failure was seen before the
named target.

## Results and smallest observed suffix

Exact focused command:

```sh
CARGO_BUILD_JOBS=1 timeout 120s cargo test -p yu-solver --features shadow-apply-candidate candidate_effect::tests::retained_local_capture_inverse_observation -- --exact --ignored --nocapture --test-threads=1
```

Exit 0. One selected ignored test passed; 663 unit tests were filtered out.
Cargo also launched package integration binaries with zero selected tests.
Compilation finished in 24.56 seconds; the selected test took 1.47 seconds.
No broad test suite, benchmark, formatting command or second Cargo run ran.

All eight sessions reached the target after 109 logged forward incidence
admissions each (872 total). Five sessions requested allocation during the
first reverse occupied-bucket insertion; each requested allocation once.
The allocating session indices were 1, 2, 4, 5 and 6. Indices 0, 3 and 7
made zero observed inverse requests. These are fresh-session indices, not
reproducible seeds, and 5/8 is not a probability claim.

In session 1, the four-operation suffix was:

| Operation | Row | Saved bucket | Before `(len, capacity)` | After `(len, capacity)` | Scoped requests |
| --- | ---: | --- | --- | --- | ---: |
| Admit occupied A | 622 | Some | (55,56) | (55,56) | 0 |
| Admit new B; fail after successful sample | 623 | None | (55,56) | (56,56) | 0 |
| Inverse B: remove | 623 | None | (56,56) | (55,55) | 0 |
| Inverse A: restore saved bucket | 622 | Some | (55,55) | (55,112) | **1** |

The other allocating sessions showed the same suffix and row identities.
The nonallocating sessions removed B without the public capacity decrement
and restored A with zero requests. This is the smallest observed operation
suffix, not a proven minimum source program. Smaller source sizes and other
source shapes were not searched under the one-source/eight-session budget.

The existing cfg(test) allocator wrapper delegates to `System` and counts
same-thread alloc/alloc_zeroed/realloc requests only around inverse `Some`
insertion. Snapshot construction, TLS setup, event append and printing are
outside that interval. The request is direct evidence that the insertion
asked for backing allocation. Public capacity is recorded as an observable;
it is not treated as raw growth credit. Zero requests do not prove absence
of an in-place rehash. Raw table layout and failed allocation are unobserved.

All eight rollback paths passed the existing `RouteCheckpoint::assert_restored`
inventory plus exact incidence-map, record-vector, incidence-key-set,
context-checkpoint, source-frame and local-route-count comparisons.
`local_use` was empty again. The checkpoint verifies terms, facts/provenance,
rows/metadata/bounds, typed work/memo, diagnostics and logical counters, with
its existing allowances for retained physical capacity and resource samples.
Physical capacities/high-water accounting need not equal their entry values;
the experiment claims logical restoration, not byte-identical storage.
Context checkpoint equality is its implemented inventory, not a separate
deep equality proof of every context map.

## Claim class, budget and limitations

Bounded source-qualified counterexample observation: this source's actual
Local route admits a failure prefix whose reverse occupied-key insertion
requests allocation in five sampled runs. It refutes allocation-free inversion
for every such observed Local-route prefix on this linked runtime, conditional
on the permitted post-sample injected failure exposing the reverse sequence.
It is not a general source theorem, an allocator-failure reproduction,
independent proof review or production authorization. W/A3 and the remaining
rollback/accounting/source-lifecycle gates remain OPEN.

Resource use: one Cargo process with `CARGO_BUILD_JOBS=1`, serial selected
test execution, eight fresh source sessions, one Oracle process, zero seed
sweeps and zero mutations. One process sample saw cargo RSS 33,920 KiB and
rustc RSS 99,464 KiB; these are samples, not peaks. Peak memory and total CPU
time were not measured. The Cargo run completed below its 120-second kill
bound and the Oracle completed below its 30-second bound.

Unverified: smaller sources, other function annotations, other platforms or
Rust/hash-map versions, allocator failure, resumed/suspended LocalUse state,
full solver orchestration and scheme publication, other mutation owners,
all-history rollback guarantees, effect hygiene, soundness/principality and
F5 production cutover. No claim that the experiment closes the parent theorem.
The run used rustc 1.95.0 (`59807616e`, 2026-04-14) and Cargo 1.95.0
(`f2d3ce0bd`, 2026-03-21).

Recommended next action: primary inspection of this frozen actual-Local
source correspondence and observer scope, then route the observed inverse
allocation premise to the authorized storage-repair owner while keeping
retained pause/resume correspondence explicit.

## Commit packet

Exact leased paths:

- `crates/yu-solver/src/candidate_effect.rs` (cfg(test) observer additions and
  one ignored research test only; production unchanged).
- `notes/progress/2026-10-11-retained-local-capture-observation.md`.

Baseline SHA: `0d643a144baec574881af97ff82d841b5352a518`.
Direct read dependencies rechecked unchanged:

| Path | SHA-256 |
| --- | --- |
| `candidate_source.rs` | `13f5d3eebeaac00e298878da0b1f7b7e7335bb88baa93c875056237501be1a49` |
| `candidate_scheme.rs` | `9c14664b4962ffe72a50e8b13bfda5dcec3d3731dcf8b61a65f9a196a9df18c1` |
| `candidate_extrusion.rs` | `fd360f784a763b9d76824b630eec2e9665cf1b9c44775246718ce9ae91315ff0` |
| `lib.rs` | `c21376746b2c6d022d4e7c709c0c88e61d8b9c10eb260d617479f4f10b901a94` |
| `candidate_intrusion.rs` | `aec3ad6e6028a1a358b622a8d34723e43bde70282695ebc2415876a08dfbceb0` |
| `candidate_context.rs` | `4385c96423cd5c6cd1686066b2e6f0581c5cebf47d68bc86476c79e2a2f88987` |
| private suspension contract | `734d94cb02c3d2a101ab21435b4377ed06952ab384815da73636bcfbc986033d` |
| earlier native probe note | `258f6658d50e7f77eb492e70d8fc7008dc615b0b758e93d99a69af1654a76b17` |

The leased code began at SHA-256
`928d7846e14d8cabe34087cc597151957b38ae374060f9d8595d69b4b000dcde`.
No read-dependency hash changed; the final leased-output hashes are supplied
in the producer handoff. The sole post-check code change is a comment
clarifying vector residence. Checks already run: exact focused Cargo command
and one frozen-Oracle dump above, plus narrow diff/hash inspection.
Review status: unreviewed frozen research; primary inspection pending.
Proposed checkpoint message: `research: observe capture inverse allocation in actual Local route`.
Shared-record deltas intentionally deferred to primary/curator:
`tasks/current.md` should record actual Local-route reachability, 8/8 targets,
5/8 allocation sessions, the vector-residence limitation, and the remaining
OPEN theorem/lifecycle/storage premises. No task, index, authority, question
bundle or theory-map file was edited.
